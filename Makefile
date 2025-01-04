# Nom du fichier binaire final
EXEC = mitm_mpi

# Nom du fichier source
SRC = mitm_mpi_Cyprien_Renaud_Francis_Jegou.c

# Compilateur
CC = mpicc

# Options de compilation
CFLAGS = -Wall

# Règle par défaut
all: $(EXEC)

# Règle pour construire le fichier exécutable
$(EXEC): $(SRC)
	$(CC) $(CFLAGS) -o $(EXEC) $(SRC)

# Règle pour nettoyer les fichiers générés
clean:
	rm -f $(EXEC)

# Règle pour forcer la recompilation
rebuild: clean all
