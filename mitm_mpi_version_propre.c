#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <assert.h>
#include <getopt.h>
#include <err.h>
#include <assert.h>
#include <string.h>


#include <mpi.h>
#include <omp.h>

typedef uint64_t u64;       /* portable 64-bit integer */
typedef uint32_t u32;       /* portable 32-bit integer */
struct __attribute__ ((packed)) entry { u32 k; u64 v; };  /* hash table entry */

/***************************** global variables ******************************/

u64 n = 0;         /* block size (in bits) */
u64 mask;          /* this is 2**n - 1 */

u64 dict_size;     /* number of slots in the hash table */
struct entry *A;   /* the hash table */

/* (P, C) : two plaintext-ciphertext pairs */
u32 P[2][2] = {{0, 0}, {0xffffffff, 0xffffffff}};
u32 C[2][2];

/************************ tools and utility functions *************************/

double wtime()
{
	struct timeval ts;
	gettimeofday(&ts, NULL);
	return (double)ts.tv_sec + ts.tv_usec / 1E6;
}

// murmur64 hash functions, tailorized for 64-bit ints / Cf. Daniel Lemire
u64 murmur64(u64 x)
{
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdull;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ull;
    x ^= x >> 33;
    return x;
}

/* represent n in 4 bytes */
void human_format(u64 n, char *target)
{
    if (n < 1000) {
        sprintf(target, "%" PRId64, n);
        return;
    }
    if (n < 1000000) {
        sprintf(target, "%.1fK", n / 1e3);
        return;
    }
    if (n < 1000000000) {
        sprintf(target, "%.1fM", n / 1e6);
        return;
    }
    if (n < 1000000000000ll) {
        sprintf(target, "%.1fG", n / 1e9);
        return;
    }
    if (n < 1000000000000000ll) {
        sprintf(target, "%.1fT", n / 1e12);
        return;
    }
}

/******************************** SPECK block cipher **************************/

#define ROTL32(x,r) (((x)<<(r)) | (x>>(32-(r))))
#define ROTR32(x,r) (((x)>>(r)) | ((x)<<(32-(r))))

#define ER32(x,y,k) (x=ROTR32(x,8), x+=y, x^=k, y=ROTL32(y,3), y^=x)
#define DR32(x,y,k) (y^=x, y=ROTR32(y,3), x^=k, x-=y, x=ROTL32(x,8))

void Speck64128KeySchedule(const u32 K[],u32 rk[])
{
    u32 i,D=K[3],C=K[2],B=K[1],A=K[0];
    for(i=0;i<27;){
        rk[i]=A; ER32(B,A,i++);
        rk[i]=A; ER32(C,A,i++);
        rk[i]=A; ER32(D,A,i++);
    }
}

void Speck64128Encrypt(const u32 Pt[], u32 Ct[], const u32 rk[])
{
    u32 i;
    Ct[0]=Pt[0]; Ct[1]=Pt[1];
    for(i=0;i<27;)
        ER32(Ct[1],Ct[0],rk[i++]);
}

void Speck64128Decrypt(u32 Pt[], const u32 Ct[], u32 const rk[])
{
    int i;
    Pt[0]=Ct[0]; Pt[1]=Ct[1];
    for(i=26;i>=0;)
        DR32(Pt[1],Pt[0],rk[i--]);
}

/******************************** dictionary ********************************/

/*
 * "classic" hash table for 64-bit key-value pairs, with linear probing.  
 * It operates under the assumption that the keys are somewhat random 64-bit integers.
 * The keys are only stored modulo 2**32 - 5 (a prime number), and this can lead 
 * to some false positives.
 */
static const u32 EMPTY = 0xffffffff;
static const u64 PRIME = 0xfffffffb;

/* allocate a hash table with `size` slots (12*size bytes) */
void dict_setup(u64 size, int C_size, int rank)
{
	dict_size = size/C_size; //On alloue 2^N/nombre de processeurs
	char hdsize[8];
	human_format(dict_size * sizeof(*A), hdsize);
	printf("Dictionary size: %sB\n", hdsize);

	A = malloc(sizeof(*A) * dict_size);
	if (A == NULL)
		err(1, "impossible to allocate the dictionnary");
	for (u64 i = 0; i < dict_size; i++)
		A[i].k = EMPTY;
}

/* Insert the binding key |----> value in the dictionnary */
void dict_insert(u64 key, u64 value)
{
    u64 h = murmur64(key) % dict_size;
    for (;;) {
        if (A[h].k == EMPTY)
            break;
        h += 1;
        if (h == dict_size)
            h = 0;
    }
    assert(A[h].k == EMPTY);
    A[h].k = key % PRIME;
    A[h].v = value;
}

/* Query the dictionnary with this `key`.  Write values (potentially) 
 *  matching the key in `values` and return their number. The `values`
 *  array must be preallocated of size (at least) `maxval`.
 *  The function returns -1 if there are more than `maxval` results.
 */
int dict_probe(u64 key, int maxval, u64 values[])
{
    u32 k = key % PRIME;
    u64 h = murmur64(key) % dict_size;
    int nval = 0;
    for (;;) {
        if (A[h].k == EMPTY)
            return nval;
        if (A[h].k == k) {
        	if (nval == maxval)
        		return -1;
            values[nval] = A[h].v;
            nval += 1;
        }
        h += 1;
        if (h == dict_size)
            h = 0;
   	}
}

/***************************** MITM problem ***********************************/

/* f : {0, 1}^n --> {0, 1}^n.  Speck64-128 encryption of P[0], using k */
u64 f(u64 k)
{
    assert((k & mask) == k);
    u32 K[4] = {k & 0xffffffff, k >> 32, 0, 0};
    u32 rk[27];
    Speck64128KeySchedule(K, rk);
    u32 Ct[2];
    Speck64128Encrypt(P[0], Ct, rk);
    return ((u64) Ct[0] ^ ((u64) Ct[1] << 32)) & mask;
}

/* g : {0, 1}^n --> {0, 1}^n.  speck64-128 decryption of C[0], using k */
u64 g(u64 k)
{
    assert((k & mask) == k);
    u32 K[4] = {k & 0xffffffff, k >> 32, 0, 0};
    u32 rk[27];
    Speck64128KeySchedule(K, rk);
    u32 Pt[2];
    Speck64128Decrypt(Pt, C[0], rk);
    return ((u64) Pt[0] ^ ((u64) Pt[1] << 32)) & mask;
}

bool is_good_pair(u64 k1, u64 k2)
{
    u32 Ka[4] = {k1 & 0xffffffff, k1 >> 32, 0, 0};
    u32 Kb[4] = {k2 & 0xffffffff, k2 >> 32, 0, 0};
    u32 rka[27];
    u32 rkb[27];
    Speck64128KeySchedule(Ka, rka);
    Speck64128KeySchedule(Kb, rkb);
    u32 mid[2];
    u32 Ct[2];
    Speck64128Encrypt(P[1], mid, rka);
    Speck64128Encrypt(mid, Ct, rkb);
    return (Ct[0] == C[1][0]) && (Ct[1] == C[1][1]);
}

/******************************************************************************/

/* search the "golden collision" */
int golden_claw_search(int maxres, u64 k1[], u64 k2[], int rank, int size) {
    int global_nres = 0;
    double start = wtime();
    u64 N = 1ull << n; //Cela correspond à 2^n

    // Step 1 : Alloctaions des buffers pour Alltoallv
    u64 buffer_size = (2*N)/size;
    u64 *sendbuf = malloc(buffer_size* sizeof(u64));
    int *sendcounts = calloc(size, sizeof(int));
    int *recvcounts = calloc(size, sizeof(int));
    int *sdispls = calloc(size, sizeof(int));
    int *rdispls = calloc(size, sizeof(int));

    
    if (sendbuf == NULL ) { //|| recvbuf == NULL
        fprintf(stderr, "Memory allocation failed\n");
        MPI_Abort(MPI_COMM_WORLD, 1); // Terminer si l'allocation échoue
    }
    
    // Step 2 : Remplissage des dictionnaires
    // Step 2.1 : Calcul de sendcounts pour calculer sdispls
    for (u64 x = rank; x < N; x+=size) {
        u64 z = f(x);
        int shard = z % size;
        sendbuf[sendcounts[shard]++] = z; 
        sendbuf[sendcounts[shard]++] = x;
       
    }

    
    

    // Step 2.2 : Calcul de sdispls
    sdispls[0] = 0;
    for (int i = 1; i < size; ++i) {
        sdispls[i] = sdispls[i - 1] + sendcounts[i - 1];
    }
   

    // Step 2.3 : Remplissage de sendbuf
    memset(sendcounts, 0, size * sizeof(int));
    for (u64 x = rank; x < N; x+=size) {
        u64 z = f(x);
        int shard = z % size;
        int index = sdispls[shard] + sendcounts[shard];
        if (index>=(2*N)/size){
            
            // Si lbuffer_size n'est pas suffisant on alloue de la mémoire supplémentaire
            sendbuf = (u64 *)realloc(sendbuf, (2+buffer_size)* sizeof(u64));
            if (sendbuf == NULL ) { 
                fprintf(stderr, "Memory allocation failed\n");
                MPI_Abort(MPI_COMM_WORLD, 1);
            }
    
        }
        
        sendbuf[index] = z;     // Stocker z
        sendbuf[index + 1] = x; // Stocker x
       
        sendcounts[shard]+=2;
    
    }


    // Step 2.4 : Envoi de sendcounts pour recvcounts
    MPI_Alltoall(sendcounts, 1, MPI_INT, recvcounts, 1, MPI_INT, MPI_COMM_WORLD);

  
    
    // Step 2.5 : Calcul de rdisplsCompute displacements for receive
    rdispls[0] = 0;
    for (int i = 1; i < size; ++i) {
        rdispls[i] = rdispls[i - 1] + recvcounts[i - 1];
    }

    
    
    

    // Step 2.6 : Calcul du total reçu pour allouer laplace mémore de recvbuf
    int total_send = 0;
    int total_recv = 0;
    for (int i = 0; i < size; ++i) {
        total_send += sendcounts[i];
        total_recv += recvcounts[i];
    }

    // Step 2.7 : Allocation de recvbuf
    u64 *recvbuf = malloc(total_recv * sizeof(u64));
    if (recvbuf == NULL ) { //|| recvbuf == NULL
        fprintf(stderr, "Memory allocation failed\n");
        MPI_Abort(MPI_COMM_WORLD, 1); // Terminer si l'allocation échoue
    }
   


    // Step 2.8 : Lancer AlltoAllv pour distribuer les données
    MPI_Alltoallv(sendbuf, sendcounts, sdispls, MPI_UINT64_T,
                  recvbuf, recvcounts, rdispls, MPI_UINT64_T, MPI_COMM_WORLD);
    

    // Step 2.9 : Remplissage des dictionnaires
    for (int i = 0; i < rdispls[size - 1] + recvcounts[size - 1]; i += 2) {
        u64 z = recvbuf[i];
        u64 x = recvbuf[i + 1];
        dict_insert(z, x);
    }
    
    // Step 2.10 : Libération de la mémoire
    free(recvbuf);
    

    double mid = wtime();
    if (rank == 0) {
        printf("Fill: %.1fs\n", mid - start);
    }

    // Step 3 : Recherche des solutions, on refait la méthode de distribution des données
    // Step 3.1 : Remise des buffers à 0
    memset(sendcounts, 0, size * sizeof(int));
    memset(sdispls, 0, size * sizeof(int));
    memset(recvcounts, 0, size * sizeof(int));
    memset(rdispls, 0, size * sizeof(int));
  
    //Step 3.2 : On refait la méthode de distribution des données
    for (u64 x = rank; x < N; x+=size) {
        u64 z = g(x);
        int shard = z % size;
        sendbuf[sendcounts[shard]++] = z; // Pack z and x
        sendbuf[sendcounts[shard]++] = x;
    }

    
    sdispls[0] = 0;
    for (int i = 1; i < size; ++i) {
        sdispls[i] = sdispls[i - 1] + sendcounts[i - 1];
    }
    
    memset(sendcounts, 0, size * sizeof(int));
    for (u64 x = rank; x < N; x+=size) {
        u64 z = g(x);
        int shard = z % size;
        int index = sdispls[shard] + sendcounts[shard];
        if (index>=(2*N)/size){
            
            sendbuf = (u64 *)realloc(sendbuf, (2+(2*N)/size)* sizeof(u64));
            if (sendbuf == NULL ) { 
                fprintf(stderr, "Memory allocation failed\n");
                MPI_Abort(MPI_COMM_WORLD, 1); 
            }
            
        }
        sendbuf[index] = z;     // Stocker z
        sendbuf[index + 1] = x; // Stocker x
        
        sendcounts[shard]+=2;
    
    }


    MPI_Alltoall(sendcounts, 1, MPI_INT, recvcounts, 1, MPI_INT, MPI_COMM_WORLD);

   
    rdispls[0] = 0;
    for (int i = 1; i < size; ++i) {
        rdispls[i] = rdispls[i - 1] + recvcounts[i - 1];
    }

    total_send = 0;
    total_recv = 0;
    for (int i = 0; i < size; ++i) {
        total_send += sendcounts[i];
        total_recv += recvcounts[i];
    }
    recvbuf = malloc(total_recv * sizeof(u64));
    if (recvbuf == NULL ) { 
        fprintf(stderr, "Memory allocation failed\n");
        MPI_Abort(MPI_COMM_WORLD, 1); // Terminer si l'allocation échoue
    }
    
    MPI_Alltoallv(sendbuf, sendcounts, sdispls, MPI_UINT64_T,
                  recvbuf, recvcounts, rdispls, MPI_UINT64_T, MPI_COMM_WORLD);

    int nres = 0;
    u64 ncandidates = 0;
    u64 results[256];


    // Step 3.3 : Recherche des solutions
    for (u64 i = 0; i< rdispls[size - 1] + recvcounts[size - 1]; i ++) { 
        u64 z = recvbuf[i];
        u64 y = recvbuf[i+1];
        
        int nx = dict_probe(z, 256, results);
     
        assert(nx >= 0);
        ncandidates += nx;
        for (int i = 0; i < nx; ++i) {
            if (is_good_pair(results[i], y)) {
                printf("Process %d: Good pair found: x=%" PRIu64 ", z=%" PRIu64 "\nnres = %d, maxres = %d\n", rank, results[i], z,nres,maxres);
                
                
                if (nres == maxres) {
                    
                    return -1;
                }
                
                
                k1[nres] = results[i];
                k2[nres] = y;
                
                
                printf("SOLUTION FOUND!\n");
                
                nres += 1;
                
                
            
                
            }
            
        }
        
    
            
    }
    

    
    // Step 4 : Calcul du nombre total de candidats
    MPI_Barrier(MPI_COMM_WORLD);
    
    
    int total_nres;
    
    MPI_Allreduce(&nres, &total_nres, 1, MPI_INT, MPI_MAX, MPI_COMM_WORLD);
    
    u64 global_ncandidates = 0;
    MPI_Reduce(&ncandidates, &global_ncandidates, 1, MPI_UINT64_T, MPI_SUM, 0, MPI_COMM_WORLD);
    

    double end = wtime();
    if (rank == 0) {
        printf("Probe: %.1fs. %" PRId64 " candidate pairs tested\n", end - mid, global_ncandidates);
    }

    return total_nres;
}


/************************** command-line options ****************************/

void usage(char **argv)
{
        printf("%s [OPTIONS]\n\n", argv[0]);
        printf("Options:\n");
        printf("--n N                       block size [default 24]\n");
        printf("--C0 N                      1st ciphertext (in hex)\n");
        printf("--C1 N                      2nd ciphertext (in hex)\n");
        printf("\n");
        printf("All arguments are required\n");
        exit(0);
}

void process_command_line_options(int argc, char ** argv)
{
        struct option longopts[4] = {
                {"n", required_argument, NULL, 'n'},
                {"C0", required_argument, NULL, '0'},
                {"C1", required_argument, NULL, '1'},
                {NULL, 0, NULL, 0}
        };
        char ch;
        int set = 0;
        while ((ch = getopt_long(argc, argv, "", longopts, NULL)) != -1) {
                switch (ch) {
                case 'n':
                        n = atoi(optarg);
                        mask = (1ull << n) - 1;
                        break;
                case '0':
                        set |= 1;
                        u64 c0 = strtoull(optarg, NULL, 16);
                        C[0][0] = c0 & 0xffffffff;
                        C[0][1] = c0 >> 32;
                        break;
                case '1':
                        set |= 2;
                        u64 c1 = strtoull(optarg, NULL, 16);
                        C[1][0] = c1 & 0xffffffff;
                        C[1][1] = c1 >> 32;
                        break;
                default:
                        errx(1, "Unknown option\n");
                }
        }
        if (n == 0 || set != 3) {
        	usage(argv);
        	exit(1);
        }
}

/******************************************************************************/

/*
 * Liste des tags
 * tag = 0 => Envoie du dictionnaire vide dans chaque processus
 * tag = 1 => Envoie de x au processus n°shard
 * tag = 2 => Envoie de z au processus n°shard
 * tag = 3 => Envoie de y au processus n°shard
 * tag = 4 => Envoie de w au processis n°shard
 * tag = 5 =>
 */

int main(int argc, char **argv)
{
	process_command_line_options(argc, argv);
    printf("Running with n=%d, C0=(%08x, %08x) and C1=(%08x, %08x)\n", 
        (int) n, C[0][0], C[0][1], C[1][0], C[1][1]);
    
    MPI_Init(&argc, &argv);

    int rank;
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);

    int C_size;
    MPI_Comm_size(MPI_COMM_WORLD, &C_size);

    int root_rank = 0;

	dict_setup(1.125 * (1ull << n), C_size, rank);

	/* search */
    // Step 5 : Fusion des résultats
	u64 k1[16], k2[16];
    for(int i=0; i<16; i++){
        k1[i]=0;
        k2[i]=0;
    }

	int nkey = golden_claw_search(16, k1, k2, rank, C_size);
	assert(nkey > 0);

    u64 global_k1[16 * C_size];
    u64 global_k2[16 * C_size];
    
    MPI_Gather(k1, 16, MPI_UINT64_T, global_k1, 16, MPI_UINT64_T, 0, MPI_COMM_WORLD);
    MPI_Gather(k2, 16, MPI_UINT64_T, global_k2, 16, MPI_UINT64_T, 0, MPI_COMM_WORLD);
    
    /* validation */
    // Step 6 : Validation des résultats
    if (rank == 0) {
        for (int i = 0; i < 16 * C_size; i++) {
            //printf("global_k1 = %ld, global_k2 = %ld\n",global_k1[i],global_k2[i]);
            if (global_k1[i] != 0 || global_k2[i] != 0) { // Skip empty slots
                assert(f(global_k1[i]) == g(global_k2[i]));
                assert(is_good_pair(global_k1[i], global_k2[i]));
                printf("Solution found: (%" PRIx64 ", %" PRIx64 ") [checked OK]\n", global_k1[i], global_k2[i]);
            }
        }
    }

    MPI_Finalize();
    

    
    
}