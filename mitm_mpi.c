#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>
#include <assert.h>
#include <getopt.h>
#include <err.h>
#include <assert.h>

#include <mpi.h>


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

int rank, C_size;
MPI_Status status;

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
void dict_setup(u64 size)
{
	// dict_size = 2*size/(C_size-1); // size
    dict_size = size;
	char hdsize[8];
	human_format(dict_size * sizeof(*A), hdsize);
	printf("Dictionary size: %sB\n", hdsize);

	A = malloc(sizeof(*A) * dict_size);
	if (A == NULL)
		err(1, "impossible to allocate the dictionnary");
	for (u64 i = 0; i < dict_size; i++)
		A[i].k = EMPTY;

    /*
    // envoyer le tableau à chaque processus ou l'initialiser dans chaque processus (sendi pour passer à autre chose)
    // on peut faire une boucle for 
    for(u64 i = 1; i < C_size; i++){
        MPI_sendi(&A, dict_size, MPI_UINT64T, i, 0, MPI_COMM_WORLD); // envoie du tableau de taille 2*size/(C_size-1) = dict_size au processus i
    }
    for(u64 i = 1; i < C_size; i++){
        if(rank == i){
            MPI_recvi(&A, dict_size, MPI_UINT64T, root_rank, 0, MPI_COMM_WORLD, &status); // recevoir du tableau de taille 2*size/(C_size-1) = dict_size au processus root_rank = 0
        }
    }*/
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
/*int golden_claw_search(int maxres, u64 k1[], u64 k2[])
{
    double start = wtime();
    u64 shard = 0;
    u64 N = 1ull << n;
    for (u64 x = 0; x < N; x++) {

        u64 z = f(x);
        shard = z%(C_size-1) + 1;

        MPI_sendi(&z, 1, MPI_UINT64_T, shard, 1, MPI_COMM_WORLD);
        MPI_sendi(&x, 1, MPI_UINT64_T, shard, 2, MPI_COMM_WORLD);

        if(rank == shard){

            MPI_recvi(z, dict_size, MPI_UINT64_T, root_rank, 1, MPI_COMM_WORLD, &status);
            MPI_recvi(x, dict_size, MPI_UINT64_T, root_rank, 2, MPI_COMM_WORLD, &status); 
            
            dict_insert(z, x);
        }
        
    }

    double mid = wtime();
    printf("Fill: %.1fs\n", mid - start);
    
    int nres = 0;
    u64 ncandidates = 0;
    u64 x[256];
    for (u64 z = 0; z < N; z++) {
        
        u64 y = g(z);
        shard = y%(C_size-1);

        MPI_sendi(&y, 1, MPI_UINT64_T, shard, 3, MPI_COMM_WORLD);
        MPI_sendi(&z, 1, MPI_UINT64_T, shard, 4, MPI_COMM_WORLD);

        if(rank == shard){

            MPI_recvi(y, dict_size, MPI_UINT64_T, root_rank, 3, MPI_COMM_WORLD, &status);
            MPI_recvi(z, dict_size, MPI_UINT64_T, root_rank, 4, MPI_COMM_WORLD, &status); 

            int nx = dict_probe(y, 256, x);
            assert(nx >= 0);
            ncandidates += nx;
            for (int i = 0; i < nx; i++){
                if (is_good_pair(x[i], z)) {
                    if (nres == maxres)
                        return -1;
                    k1[nres] = x[i];
                    k2[nres] = z;
                    printf("SOLUTION FOUND!\n");
                    nres += 1;
                }
            }
            
        }
        // il faut récupérer tous les k1 et les k2 dans le processus mere
        if(rank == root_rank){
            // MPI_reduce ou quelque chose comme ça
            // récupérer le nres de chaque processus, faire la somme 
            // et vérifier si on dépasse maxres et return -1 si c'est on dépasse
        }
    }
    printf("Probe: %.1fs. %" PRId64 " candidate pairs tested\n", wtime() - mid, ncandidates);
    return nres;
}*/

int root_rank = 0;
/*
int golden_claw_search(int maxres, u64 k1[], u64 k2[])
{
    double start = wtime();
    u64 shard = 0;
    u64 N = 1ull << n;

    u64 send_data[C_size * 2];
    u64 recv_data[C_size * 2];

    int root_rank = 0;

    printf("%d", N);

    for (u64 x = 0; x < N; x++) {
        u64 z = f(x);
        shard = z % (C_size - 1) + 1;

        // Préparer les données à envoyer avec MPI_Alltoall
        send_data[rank * 2] = z;
        send_data[rank * 2 + 1] = x;

        MPI_Alltoall(send_data, 2, MPI_UINT64_T, recv_data, 2, MPI_UINT64_T, MPI_COMM_WORLD);

        for (int i = 0; i < C_size; i++) {
            u64 recv_z = recv_data[i * 2];
            u64 recv_x = recv_data[i * 2 + 1];
            
            if (rank == shard) {
                dict_insert(recv_z, recv_x);
            }
        }
        printf("%d",x);
    }
    printf("ici");
    double mid = wtime();
    printf("Fill: %.1fs\n", mid - start);

    int nres = 0;
    u64 ncandidates = 0;
    u64 x[256];
    u64 local_k1[256], local_k2[256];
    int local_nres = 0;

    for (u64 z = 0; z < N; z++) {
        u64 y = g(z);
        shard = y % (C_size - 1);

        // Préparer les données à envoyer avec MPI_Alltoall
        send_data[rank * 2] = y;
        send_data[rank * 2 + 1] = z;

        MPI_Alltoall(send_data, 2, MPI_UINT64_T, recv_data, 2, MPI_UINT64_T, MPI_COMM_WORLD);

        for (int i = 0; i < C_size; i++) {
            u64 recv_y = recv_data[i * 2];
            u64 recv_z = recv_data[i * 2 + 1];

            if (rank == shard) {
                int nx = dict_probe(recv_y, 256, x);
                assert(nx >= 0);
                ncandidates += nx;

                for (int j = 0; j < nx; j++) {
                    if (is_good_pair(x[j], recv_z)) {
                        if (local_nres == 256) {
                            printf("Local buffer overflow!\n");
                            return -1;
                        }
                        local_k1[local_nres] = x[j];
                        local_k2[local_nres] = recv_z;
                        local_nres++;
                    }
                }
            }
        }
    }

    // Utilisation de MPI_Reduce pour collecter les nres totaux
    int total_nres = 0;
    MPI_Reduce(&local_nres, &total_nres, 1, MPI_INT, MPI_SUM, root_rank, MPI_COMM_WORLD);

    if (rank == root_rank) {
        if (total_nres > maxres) {
            printf("Exceeded maxres, terminating search.\n");
            return -1;
        }

        // Collecte des résultats locaux dans le processus maître
        int offset = 0;
        for (int i = 0; i < local_nres; i++) {
            k1[offset + i] = local_k1[i];
            k2[offset + i] = local_k2[i];
        }
        offset += local_nres;

        // Recevoir les résultats des autres processus
        for (int proc = 1; proc < C_size; proc++) {
            int proc_nres;
            MPI_Recv(&proc_nres, 1, MPI_INT, proc, 6, MPI_COMM_WORLD, &status);

            u64 recv_k1[256], recv_k2[256];
            MPI_Recv(recv_k1, proc_nres, MPI_UINT64_T, proc, 7, MPI_COMM_WORLD, &status);
            MPI_Recv(recv_k2, proc_nres, MPI_UINT64_T, proc, 8, MPI_COMM_WORLD, &status);

            for (int i = 0; i < proc_nres; i++) {
                k1[offset + i] = recv_k1[i];
                k2[offset + i] = recv_k2[i];
            }
            offset += proc_nres;
        }
    } else {
        // Envoyer les résultats locaux au processus maître
        MPI_Send(&local_nres, 1, MPI_INT, root_rank, 6, MPI_COMM_WORLD);
        MPI_Send(local_k1, local_nres, MPI_UINT64_T, root_rank, 7, MPI_COMM_WORLD);
        MPI_Send(local_k2, local_nres, MPI_UINT64_T, root_rank, 8, MPI_COMM_WORLD);
    }

    printf("Probe: %.1fs. %" PRId64 " candidate pairs tested\n", wtime() - mid, ncandidates);
    return total_nres;
}
*/ // Programme avec alltoall qui ne fonctionne pas
/*
int golden_claw_search(int maxres, u64 k1[], u64 k2[])
{
    double start = wtime();
    u64 shard = 0;
    u64 N = 1ull << n;

    for (u64 x = 0; x < N; x++) {
        u64 z = f(x);
        shard = z % (C_size - 1) + 1;
        // printf("%d", shard);

        MPI_Send(&z, 1, MPI_UINT64_T, shard, 1, MPI_COMM_WORLD);
        MPI_Send(&x, 1, MPI_UINT64_T, shard, 2, MPI_COMM_WORLD);

        if (rank == shard) {
            MPI_Recv(&z, dict_size, MPI_UINT64_T, root_rank, 1, MPI_COMM_WORLD, &status);
            MPI_Recv(&x, dict_size, MPI_UINT64_T, root_rank, 2, MPI_COMM_WORLD, &status);

            dict_insert(z, x);
        }
    }

    double mid = wtime();
    printf("Fill: %.1fs\n", mid - start);

    int nres = 0;
    u64 ncandidates = 0;
    u64 x[256];
    for (u64 z = 0; z < N; z++) {

        u64 y = g(z);
        shard = y % (C_size - 1) + 1;

        // MPI_Send(&y, 1, MPI_UINT64_T, shard, 3, MPI_COMM_WORLD);
        // MPI_Send(&z, 1, MPI_UINT64_T, shard, 4, MPI_COMM_WORLD);

        printf("On cast les val : %d \n", rank);

        MPI_Bcast(&y, 1, MPI_UINT64_T, shard, MPI_COMM_WORLD);
        MPI_Bcast(&z, 1, MPI_UINT64_T, shard, MPI_COMM_WORLD);
        MPI_Bcast(&x, 1, MPI_UINT64_T, shard, MPI_COMM_WORLD);

        if (rank == shard) {

            // MPI_Recv(&y, dict_size, MPI_UINT64_T, root_rank, 3, MPI_COMM_WORLD, &status);
            // MPI_Recv(&z, dict_size, MPI_UINT64_T, root_rank, 4, MPI_COMM_WORLD, &status);

            printf("on se place dans le bon processus \n");

            int nx = dict_probe(y, 256, x);
            
            printf("le nb: %d ",nx);
            assert(nx >= 0);
            ncandidates += nx;
            printf("ca commence ");
            for (int i = 0; i < nx; i++) {
                // printf("ici ");
                if (is_good_pair(x[i], z)) {
                    printf("ici1");
                    if (nres == maxres)
                        return -1;
                    k1[nres] = x[i];
                    k2[nres] = z;
                    printf("SOLUTION FOUND!\n");
                    nres += 1;
                }
            }
            printf("il faut recommencer \n");
        }

        // Collect all k1, k2, and nres in the root process
        u64 global_k1[maxres * C_size];
        u64 global_k2[maxres * C_size];
        int global_nres;

        MPI_Gather(k1, nres, MPI_UINT64_T, global_k1, maxres, MPI_UINT64_T, root_rank, MPI_COMM_WORLD);
        MPI_Gather(k2, nres, MPI_UINT64_T, global_k2, maxres, MPI_UINT64_T, root_rank, MPI_COMM_WORLD);
        MPI_Reduce(&nres, &global_nres, 1, MPI_INT, MPI_SUM, root_rank, MPI_COMM_WORLD);

        if (rank == root_rank) {
            // Check if total results exceed maxres
            if (global_nres > maxres) {
                printf("Max results exceeded!\n");
                return -1;
            }

            // Consolidate k1 and k2
            for (int i = 0; i < global_nres; i++) {
                k1[i] = global_k1[i];
                k2[i] = global_k2[i];
            }
        }
    }

    printf("Probe: %.1fs. %" PRId64 " candidate pairs tested\n", wtime() - mid, ncandidates);

    int total_nres;
    MPI_Reduce(&nres, &total_nres, 1, MPI_INT, MPI_SUM, root_rank, MPI_COMM_WORLD);

    return total_nres;
} */

int golden_claw_search(int maxres, u64 k1[], u64 k2[]) {
    double start = wtime();
    u64 shard = 0;
    u64 N = 1ull << n;

    // Allocation des résultats globaux
    u64 *global_k1 = NULL;
    u64 *global_k2 = NULL;
    if (rank == root_rank) {
        global_k1 = malloc(maxres * C_size * sizeof(u64));
        global_k2 = malloc(maxres * C_size * sizeof(u64));
    }

    // Première phase : insertion dans le dictionnaire distribué
    for (u64 x = 0; x < N; x++) {
        u64 z = f(x);
        shard = z % C_size;  // Répartition entre les processus

        // Broadcast des données
        MPI_Bcast(&z, 1, MPI_UINT64_T, shard, MPI_COMM_WORLD);
        MPI_Bcast(&x, 1, MPI_UINT64_T, shard, MPI_COMM_WORLD);

        // Chaque processus insère si shard == rank
        if (rank == shard) {
            dict_insert(z, x);
        }
    }

    double mid = wtime();
    printf("Fill: %.1fs\n", mid - start);

    // Deuxième phase : recherche des correspondances
    int nres = 0;
    u64 ncandidates = 0;
    u64 x[256];

    for (u64 z = 0; z < N; z++) {
        u64 y = g(z);
        shard = y % C_size;

        // printf("envoie des données: y = %d, z = %d (rank = %d)\n", y, z, rank);

        // Broadcast des données
        MPI_Bcast(&y, 1, MPI_UINT64_T, shard, MPI_COMM_WORLD);
        MPI_Bcast(&z, 1, MPI_UINT64_T, shard, MPI_COMM_WORLD);

        if (rank == shard) {
            // printf("je suis dans le shard : %d \n", shard);

            int nx = dict_probe(y, 256, x);
            // printf("on a %d candidats à tester \n", nx);

            assert(nx >= 0);
            ncandidates += nx;

            for (int i = 0; i < nx; i++) {
                if (is_good_pair(x[i], z)) {
                    if (nres == maxres) {
                        free(global_k1);
                        free(global_k2);
                        return -1;  // Trop de résultats
                    }
                    k1[nres] = x[i];
                    k2[nres] = z;
                    printf("SOLUTION FOUND!\n");
                    nres++;
                }
            }
            // printf("on a fini les tests, il faut recommencer \n");
        }
    }

    MPI_Barrier(MPI_COMM_WORLD);

    printf("on collecte les resultats \n");

    // Collecte des résultats
    MPI_Gather(k1, 16, MPI_UINT64_T, global_k1, maxres, MPI_UINT64_T, root_rank, MPI_COMM_WORLD);
    MPI_Gather(k2, 16, MPI_UINT64_T, global_k2, maxres, MPI_UINT64_T, root_rank, MPI_COMM_WORLD);

    printf("on reduit les resultats \n");

    MPI_Barrier(MPI_COMM_WORLD);

    // Réduction pour calculer le nombre total de solutions
    int total_nres;
    MPI_Reduce(&nres, &total_nres, 1, MPI_INT, MPI_SUM, root_rank, MPI_COMM_WORLD);

    MPI_Barrier(MPI_COMM_WORLD);

    printf("nombre de paires trouvé : %d \n", total_nres);

    printf("on passe à l'étape suivante \n");

    if (rank == root_rank) {
        // Vérifiez si le total dépasse le maximum autorisé
        if (total_nres > maxres) {
            printf("Max results exceeded!\n");
            return -1;
        }

        // Consolidation des résultats globaux
        for (int i = 0; i < total_nres; i++) {
            k1[i] = global_k1[i];
            k2[i] = global_k2[i];
        }
    }

    printf("Probe: %.1fs. %" PRId64 " candidate pairs tested\n", wtime() - mid, ncandidates);

    // total_nres = 1;
    if(rank == root_rank) return total_nres;
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

// MPI_Alltoall
/**
 * +-----------------------+ +-----------------------+ +-----------------------+
 * |       Process 0       | |       Process 1       | |       Process 2       |
 * +-------+-------+-------+ +-------+-------+-------+ +-------+-------+-------+
 * | Value | Value | Value | | Value | Value | Value | | Value | Value | Value |
 * |   0   |  100  |  200  | |  300  |  400  |  500  | |  600  |  700  |  800  |
 * +-------+-------+-------+ +-------+-------+-------+ +-------+-------+-------+
 *     |       |       |_________|_______|_______|_________|___    |       |
 *     |       |    _____________|_______|_______|_________|   |   |       |
 *     |       |___|_____________|_      |      _|_____________|___|       |
 *     |      _____|_____________| |     |     | |_____________|_____      |
 *     |     |     |               |     |     |               |     |     |
 *  +-----+-----+-----+         +-----+-----+-----+         +-----+-----+-----+
 *  |  0  | 300 | 600 |         | 100 | 400 | 700 |         | 200 | 500 | 800 |
 *  +-----+-----+-----+         +-----+-----+-----+         +-----+-----+-----+
 *  |    Process 0    |         |    Process 1    |         |    Process 2    |
 *  +-----------------+         +-----------------+         +-----------------+
 **/

// MPI_Alltoall(&my_values, 1, MPI_INT, buffer_recv, 1, MPI_INT, MPI_COMM_WORLD);

int main(int argc, char **argv)
{
	process_command_line_options(argc, argv);
    printf("Running with n=%d, C0=(%08x, %08x) and C1=(%08x, %08x)\n", 
        (int) n, C[0][0], C[0][1], C[1][0], C[1][1]);

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &rank);
    MPI_Comm_size(MPI_COMM_WORLD, &C_size);

	dict_setup(1.125 * (1ull << n));

	/* search */
	u64 k1[16], k2[16];
	int nkey = golden_claw_search(16, k1, k2);
    // if(rank = root_rank)
    MPI_Finalize();
    printf("nombre de clé trouvé %d \n", nkey);
	assert(nkey > 0);

	/* validation */
	for (int i = 0; i < nkey; i++) {
    	assert(f(k1[i]) == g(k2[i]));
    	assert(is_good_pair(k1[i], k2[i]));		
	    printf("Solution found: (%" PRIx64 ", %" PRIx64 ") [checked OK]\n", k1[i], k2[i]);
	}

    return 0;
}