#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/timeb.h>
#include <conio.h>
#include <ctype.h>

#define MIN_V 5
#define MED_V 63
#define MAX_V 80
#define MIN_K 3
#define MAX_K 15
#define MIN_T 1
#define MAX_T 15
#define MAX_M 15

#define MAX_COVER 1024

#define ERR_WRONG_NUMBER_ARGS 101
#define ERR_INVALID_V 102
#define ERR_INVALID_K 103
#define ERR_INVALID_T 104
#define ERR_INVALID_M 105
#define ERR_INVALID_VK 106
#define ERR_INVALID_KT 107
#define ERR_INVALID_KM 108
#define ERR_INVALID_COMB 109

#define TIME_STRINGLEN 26

#define rnd(num) (rand() % (num)) /* gives an integer random number between 0 and num - 1, inclusive */

unsigned long C[MAX_V+1][MAX_K+1];	// used to calculate combination C(x,y), need 64 bits for C(p,8) when p>=64

int *Tset;		// boolean array, indicates if a t-set is covered

int Kaux[MAX_K];	// auxiliar to calculate k-sets, used in FindNextCover

int M[MAX_M];	// auxiliar to calculate m-subsets, used in SetICover, AddCoverFromRoll
int SubK[MAX_M]; // subconjunto de um volante K com elementos variando de t a m
int SubVK[MAX_M]; // subconjunto com elementos que não estão em um volante K com elementos variando de m-t a m-1

int V[MAX_V];	// auxiliar to calculate numbers that are not in a k-set

int **MTIndex;	// auxiliar to precalculate all C(m,t) combinations

int ***KXIndex;	// auxiliar to precalculate all C(k,t0) combinations, varying t0 from t to m
int ***VXIndex;	// auxiliar to precalculate all C(v-k,m-t0) combinations, varying t0 from t to m-1

unsigned long  ArrayCover [MAX_COVER];	// holds coverings
int CoverCount = 0;	// counts number of coverings
unsigned long  Size = 0;		// counts number of drawns, C(v,m)
int *ICover;		// holds the indexes of the cover that covers a combination
int *ICoverAux;		// backup of ICover

int v,k,t,m;	// v = max number, k = numbers per set, t = guarantee, m = drawn

// fill all C(v,k) combinations
// baseado na Relacao de Stiffel do triangulo de Pascal
// C(n,p) + C(n,p+1)=C(n+1,p+1)
void FillC()
{
	int i,j;
	for(i=0; i<=v; i++) 
	{
		C[i][0] =  1;
		for(j=1; j<=k; j++) 
		{
			if (i < j) 
				C[i][j] = 0;
			else
				C[i][j] = C[i-1][j-1] + C[i-1][j];
		}
	}
}

// preenche Array com as todas as combinacoes prontas
// ex: x=6,y=3 gera (0,1,2),(0,1,3).... (3,4,5)
void FillCombArray (int **Array, int x, int y)
{
	int i;
	int tCount = 0;

	// safe
	if (y > x || !y)
		return;

	for (i=0 ; i < y ; i++)
		Array[tCount][i] = i;

	while (Array[tCount][0] < x-y)
	{
		int j = 0;
		while(j<y-1 && Array[tCount][j+1] <= Array[tCount][j] + 1)
			j++;
		tCount++;
		Array[tCount][j] = Array[tCount-1][j]+1;
		for(i = 0; i < j; i++)
			Array[tCount][i] = i;
		for(i = j+1; i < y; i++)
			Array[tCount][i] = Array[tCount-1][i];
	}
}

int Initialize()
{
	unsigned long i;
	int j;

    // fill C array
	FillC();

	//alloc memory to Tset array
	Tset = (int *)malloc(C[v][t]*sizeof(int));
	if (Tset == NULL)
		return 0;
	memset(Tset,0,C[v][t]*sizeof(int));

	//alloc memory to MTIndex array
	MTIndex = (int **)malloc(C[m][t]*sizeof (int *));
	if (MTIndex == NULL)
		return 0;

	for(i = 0; i < C[m][t]; i++)
	{
		MTIndex[i] = (int *)malloc(t * sizeof(int));
		if (MTIndex[i] == NULL)
			return 0;
	}

	// fill all C(m,t) combinations
	FillCombArray(MTIndex, m, t);

	// alloc memory to KXIndex array
	// auxiliar to precalculate all C(k,t0) combinations, varying t0 from t to m
	KXIndex = (int ***)malloc((m-t+1) * sizeof(int **));
	if (KXIndex == NULL)
		return 0;

	for(j = 0; j < m-t+1; j++)
	{
		KXIndex[j] = (int **)malloc(C[k][j+t] * sizeof(int *));
		if (KXIndex[j] == NULL)
			return 0;
		for(i = 0; i < C[k][j+t]; i++)
		{
			KXIndex[j][i] = (int *)malloc((j+t) * sizeof(int));
			if (KXIndex[j][i] == NULL)
				return 0;
		}
		// fill all C(k,j+t) combinations
		FillCombArray(KXIndex[j], k, j+t);
	}

	// auxiliar to precalculate all C(v-k,m-t0) combinations, varying t0 from t to m-1
	// alloc memory to VXIndex array, only if m-t>0
	if (t < m)
	{
		VXIndex = (int ***)malloc((m-t) * sizeof(int **));
		if (VXIndex == NULL)
			return 0;

		for(j = 0; j < m-t; j++)
		{
			VXIndex[j] = (int **)malloc(C[v-k][m-j-t] * sizeof(int *));
			if (VXIndex[j] == NULL)
				return 0;
			for(i = 0; i < C[v-k][m-j-t]; i++)
			{
				VXIndex[j][i] = (int *)malloc((m-j-t) * sizeof(int));
				if (VXIndex[j][i] == NULL)
					return 0;
			}
			// fill all C(v-k,m-j-t) combinations
			FillCombArray(VXIndex[j], v-k, m-j-t);
		}
	}

	// number of possible drawns
	Size = C[v][m];

	// initialize cover index array
	ICover    = malloc(Size*sizeof(int));
	if(ICover == NULL)
		return 0;

	ICoverAux = malloc(Size*sizeof(int));
	if(ICoverAux == NULL)
		return 0;

	for(i = 0; i < Size; i++)
		ICover[i] = ICoverAux[i] = MAX_COVER;

	//initialize Random
	srand( (unsigned)time( NULL ) );

	return 1;
}
void Finalize()
{
	unsigned long i;
	unsigned long l;
	int j;

	for (l=0;l<Size;l++)
	{
		if (ICover[l] >= MAX_COVER)
			printf ("%u not covered\n",l);
	}
	
	// cover index
	if (ICoverAux)
		free(ICoverAux);
	if (ICover)
		free(ICover);

	if (t < m) 
	{
		// free VXIndex
		for(j = 0; j < m-t; j++)
		{
			for(i = 0; i < C[v-k][m-j-t]; i++)
			{
				if (VXIndex[j][i])
					free(VXIndex[j][i]);
			}
			if (VXIndex[j])
				free(VXIndex[j]);
		}
		if (VXIndex)
			free(VXIndex);
	}

	// free KXIndex
	for(j = 0; j < m-t+1; j++)
	{
		for(i = 0; i < C[k][j+t]; i++)
		{
			if (KXIndex[j][i])
				free(KXIndex[j][i]);
		}
		if (KXIndex[j])
			free(KXIndex[j]);
	}
	if (KXIndex)
		free(KXIndex);

	// free MTIndex
	for (i=0; i<C[m][t]; i++)
	{
		if (MTIndex[i])
			free(MTIndex[i]);
	}
	if (MTIndex)
		free(MTIndex);

	// free boolean array
	if (Tset)
		free(Tset);
}

// code a p-set into an unsigned long
unsigned long Code(int *A, int p)
{
	unsigned long r=0;
	int i;
	for (i=0;i<p;i++)
		r += C[A[i]][i+1];
	return r;
}

// decode a p-set into an array of int
void Decode (unsigned long num, int *A, int p)
{
	int i,j;
	for(i = p-1; i >= 0; i--) 
	{
		j = i;
		while(C[j+1][i+1] <= num)
		  j++;
		num -= C[j][i+1];
		A[i] = j;
	}
}

void PrintCover(char *FileName)
{
	int K[MAX_K];	// auxiliar to decode k-sets

	FILE *stream;
	int i;
	int l_size = 0;
	errno_t err;

	err = fopen_s(&stream, FileName, "w" );
    
	if (err != 0)
	{
		printf("Could not write to file %s\n", FileName);
		return;
	}
    // Imprime o Array de Cobertura
	for (i=0;i<CoverCount;i++)
    {
		if (ArrayCover[i] != (unsigned long)-1)
		{
			int j;
			Decode (ArrayCover[i], K, k);
			for (j=0;j<k;j++)
				fprintf( stream, "%02d\t", K[j]+1 );
			fprintf( stream, "\n");
			l_size ++;
		}
    }   
	fprintf( stream, "size of cover = %02d ",l_size );
	fclose(stream);
}

int GETSOL(int *A, int *B) 
{ 
	int i;
	unsigned long index = 0;
	for (i=0;i<t;i++)
		index += C[A[B[i]]][i+1];	// 32 bits are enough for C(v,t)
	return Tset[index]; 
}

void SETSOL(int *A, int *B)
{ 
	int i;
	unsigned long index = 0;
	for (i=0;i<t;i++)
		index += C[A[B[i]]][i+1];	// 32 bits are enough for C(v,t)
	Tset[index]=1;
}

void ADDSOL (int *K)
{
	unsigned long i;

	for (i=0; i<C[k][t]; i++)
		SETSOL(K, KXIndex[0][i]);
}

int SOLVED (int *M)
{	
	unsigned long i;
	int r = 0;

	for (i=0; !r && i<C[m][t]; i++)
		r = GETSOL(M, MTIndex[i]);

    return r;
}


// A é um array de dezenas de tamanho x
// B é um array de dezenas de tamanho y
// match é o numero esperado de elementos comuns
// retorna 1 ou 0 se o numero de elementos comuns é maior ou igual ao esperado
int MATCH (int *A, int x, int *B, int y, int match)
{
	int i, j;
	int r=0;

	for (i=0;i<x;i++)
	{
		for (j=0; j<y; j++)
			if (A[i] == B[j])
			{
				r++;
				break;
			}
		if (r == match)
			return 1;
	}
	return 0;
}

int IndexOf(int *pArray, int value, int StartPos, unsigned long Len)
{
	unsigned long i;
	for(i=StartPos;i<Len;i++)
	{
		if(pArray[i] == value)
			return i;
	}
	return -1;
}

// puts in V all elements that are not in K
void DiffVK (int *K)
{
	int i,j;
	int notinA = 0;

	// puts in V all elements that are not in K
	for(i=0, j=0; i<v; i++)
	{
	  if (j<k && K[j] == i)
		  j++;
	  else
	  {
		  V[notinA] = i;
		  notinA++;
	  }
	}
}

// seta o array ICover
// indice corresponde a um possivel sorteio
// valor corresponde a qual volante esta cobrindo
void SetICover (int *Mparam, int cover)
{
	unsigned long cm;
	cm = Code(Mparam, m);
	if (ICover[cm] > cover)
		ICover[cm] = cover;
}

// union de dezenas de A e B, e jogando em Mparam
// x = numero de dezenas de A
// y = numero de dezenas de B
// x+y = m 
void Union(int *Mparam, int *A, int x, int *B, int y)
{
	int i,ix,iy;

	// safe
	if((x+y) != m)
	{
		printf("Invalid parameters to Union %d %d",x,y);
		return;
	}
	ix = 0;
	iy = 0;
	for (i=0; i<m; i++)
	{
		// faz o union na ordem para evitar o sort
		if (iy >= y || (ix < x && A[ix] < B[iy]))
		{
			Mparam[i] = A[ix];
			ix++;
		}
		else
		{
			Mparam[i] = B[iy];
			iy++;
		}
	}
}

// preencher o array ICover com todos os volantes derivados de K
void FillICover (int *K, int cover)
{
	unsigned long i, vi;
	int j, vj;
	int t0;

	// construcao de todos os conjuntos de m dezenas que fariam t acertos 
	// a partir de um volante com k dezenas
	// * supondo C(40,6,3,5) - volante = (0,1,2,3,4,5)
	// [1] constroi subconjuntos de t0 elementos a partir de k = C(k, t0), começando com t0=t
	// * subconjuntos (0,1,2),(0,1,3),(0,1,4),...,(3,4,5)
	// [2] constroi subconjuntos com m-t0 elementos, que não estão em k = C(v-k, m-t0)
	// * (6,7),(6,8),(6,9),...,(38,39)
	// [3] faz a união dos subconjuntos, por construção o conjunto obtido faria t acertos
	// * (0,1,2,6,7),(0,1,3,6,7),....(3,4,5,38,39)
	// repete o processo até que t0 seja igual a m
	// * isso pega também os sorteios que fariam 4 e 5 acertos

	// prepara array V com elementos que não estão em K
	DiffVK(K);

	for (t0=t; t0<=m; t0++)
	{
		for (i=0; i<C[k][t0]; i++)
		{
			for (j=0; j<t0; j++)
			{
				// [1]
				SubK[j] = K[KXIndex[t0-t][i][j]]; 
			}
			// [2]
			if (t0 < m)
			{
				for (vi=0; vi<C[v-k][m-t0]; vi++)
				{
					for (vj=0; vj<m-t0; vj++)
					{
						SubVK[vj] = V[VXIndex[t0-t][vi][vj]];
					}
					// [3] - resultado do Union fica em M
					Union(M, SubK, t0, SubVK, m-t0);
					SetICover(M, cover);
				}
			}
			else
				// se t0=m, então SubK tem m elementos
				SetICover(SubK, cover);
		}
	}
}


void AddCoverCommon(int *K)
{	
	// preenche o array ICover com todos os volantes derivados de K
	FillICover(K, CoverCount);

	// adiciona um volante
	ADDSOL(K);
	// save K
	ArrayCover[CoverCount] = Code(K, k);

	CoverCount++;
	if (CoverCount == MAX_COVER)
	{
		printf("maximum number of coverings reached, aborting execution, look for incomplete.txt\n");
		PrintCover("incomplete.txt");
		Finalize();
		exit(1);
	}
}

void AddCoverFromRoll(int *K)
{
	int i,j;

	// for each C(k,m) combination
	for (i=0; i<(int)C[k][m]; i++)
	{
		for (j=0; j<m; j++)
			M[j] = K[KXIndex[m-t][i][j]];

		// check to see if it is already covered
		if(SOLVED(M) == 0)
		{
			// se não está coberto adiciona
			AddCoverCommon(K);
			break;
		}
	}
}

void Roll()
{
	int K[MAX_K];	// auxiliar to calculate k-sets

	int i;

	for (i=0 ; i < k ; i++)
		K[i] = i;

	AddCoverFromRoll(K);
	while (K[0] < v-k)
	{
		int j = 0;
		while(j<k-1 && K[j+1] <= K[j] + 1)
			j++;
		K[j]++;
		for(i = 0; i < j; i++)
			K[i] = i;
		AddCoverFromRoll(K);	
 	} 
}

int compare (const int *i, const int *j)
{
	return *i-*j;
}

// procura proxima cobertura para um volante removido
// em C(x,6,3,6) ao remover um volante (0,1,2,3,4,5)
// o sorteio (0,1,2,3,4,5) pode ser coberto por um outro jogo, exemplo: (0,1,2,7,8,9) 
int FindNextCover(unsigned long ind, int cover)
{
	int i;

	// obtem as dezenas do sorteio
	Decode(ind, M, m);

	for (i = cover+1; i < CoverCount; i++)
	{
		// ignore if already removed
		if (ArrayCover[i] != (unsigned long)-1 )
		{
			// obtem as dezenas do volante
			Decode(ArrayCover[i], Kaux, k);
			// se esse outro volante, tem t dezenas em comum com esse sorteio, retorna
			if (MATCH(M, m, Kaux, k, t))
				return i;
		}
	}
	return MAX_COVER;
}

// apenas limpa todas as entradas de um volante no ICover
void RemoveCover(int cover)
{
	unsigned long i;

	for(i=0;i<Size;i++)
	{
		if(ICover[i] == cover)
		{
			ICover[i] = MAX_COVER;
		}
	}
}

// esse método procura por sorteios não cobertos por nenhum volante
// quando encontra, tenta achar um outro volante que cubra
// se não encontra, retorna 0
// se preencheu tudo, retorna 1
int IsComplete(int cover)
{
	unsigned long i;
	int nc;

	for(i=0;i<Size;i++)
	{
		if(ICover[i] == MAX_COVER)
		{
			// try to find an alternative
			nc = FindNextCover(i, cover);
			if (nc == MAX_COVER) 
				return 0;
			ICover[i] = nc;
		}
	}
	return 1;
}

int Optimize(void)
{
	// [1] para cada volante, a partir do segundo [um volante sempre vai existir]
	// [2] se volante já não foi removido
	// [3] faz um backup do volante
	// [4] faz um backup do ICover
	// [5] remove o volante 
	// [6] pega as dezenas do volante K
	// [7] monta o conjunto V com todas as dezenas que não estão no volante K
	// [8] monta volante K', sorteia uma dezena de K e troca por uma dezena sorteada de V
	// [9] ordena K'
	// [10] preenche o ICover com esse novo volante
	// [11] se ICover esta completo, i.e., não tem nenhuma entrada MAX_COVER
	// [12] salva esse novo volante e incrementa contador de mudancas com sucesso
	// [13] senão, volta backup do volante e do array ICover
	// [14] retorna contador de mudancas com sucesso
	
	int K[MAX_K];	// auxiliar to calculate k-sets
	int mov = 0; // moving counter
	int i;
	unsigned long Kbkp;
	int ik; // indice do volante K
	int iv; // indice do conjunto V

	// [1]
	for (i=1; i<CoverCount; i++)
	{
		// [2] ignore if already removed
		if(ArrayCover[i] != (unsigned long) -1)
		{
			// try to eliminate some covering
			// if it is already covered, then try to remove
			if (IndexOf(ICover,i,0,Size) == -1)
			{
				//set to zero
				ArrayCover[i] = (unsigned long) -1;
			}
			else
			{
				// [3] e [4] backup 
				Kbkp = ArrayCover[i];
				memcpy(ICoverAux,ICover,sizeof(int)*Size);

				// [5] remove
				RemoveCover(i);

				// [6] decode into K
				Decode(Kbkp, K, k);

				// [7] puts in V all elements that are not in K
				DiffVK(K);

				// [8]
				ik = rnd(k);
				iv = rnd(v-k);
				K[ik] = V[iv];

				// [9] sort K
				qsort(K, k, sizeof(int), compare);

				// [10] preenche ICover a partir desse novo volante
				FillICover(K, i);

				// [11] se a cobertura continua completa
				if (IsComplete(i))
				{
					// [12]
					ArrayCover[i] = Code(K, k);
					mov++;
				}
				else
				{
					// [13] restore backup
					ArrayCover[i] = Kbkp;
					memcpy(ICover,ICoverAux,sizeof(int)*Size);
				}
			}
		}
	}
	// [14]
	return mov;
}

int CoverSize(void)
{
    int size = 0;
	int i;
    for(i = 0; i < CoverCount; i++)
        if (ArrayCover[i] != (unsigned long)-1) size++;
    return size;
}

int StartFromFile(char *filename)
{
	int K[MAX_K];	// auxiliar to read k-sets

	FILE *stream;

	size_t aux =0;
	int i;
	char c[2];
	char tab[1];
	errno_t err;

	err = fopen_s(&stream, filename, "r" );
	if(err != 0)
	{
		printf("%s File not found!\n",filename);
		return -1;
	}

    while (!feof(stream))
    {
		for(i=0;i<k;i++)
		{
			aux = fread(c,sizeof(char),2,stream);
			aux = fread(tab,sizeof(char),1,stream);
			if (!aux) break;
			K[i] = atoi(c)-1;
			if (K[i] >= v || K[i] < 0)
			{
				printf("Invalid value found: %d\n",K[i]+1);
				printf("%s", c);
				fclose(stream);
				return -1;
			}		
		}
		aux = fread(tab,sizeof(char),1,stream);
		if (!aux) break;
		AddCoverCommon(K);
    }
	fclose(stream);
	return 0;
}

void printHelp(int errnum)
{
	switch(errnum)
	{
	case ERR_WRONG_NUMBER_ARGS:
		printf("Wrong number of Arguments.\n");
		break;
	case ERR_INVALID_V:
		printf("Invalid value for v.\n");
		break;
	case ERR_INVALID_K:
		printf("Invalid value for k.\n");
		break;
	case ERR_INVALID_T:
		printf("Invalid value for t.\n");
		break;
	case ERR_INVALID_M:
		printf("Invalid value for m.\n");
		break;
	case ERR_INVALID_VK:
		printf("k should be less than v.\n");
		break;
	case ERR_INVALID_KT:
		printf("t should be less or equal to k.\n");
		break;
	case ERR_INVALID_KM:
		printf("m should be less or equal to k.\n");
		break;
	case ERR_INVALID_COMB:
		printf("v should be less or equal to %d when k is %d.\n", MED_V, MAX_K);
		break;
	}
	printf("Use: coverc v k t m out [in]\n");
	printf("v = max number [%d-%d]\nk = numbers per set [%d-%d]\nt = guarantee [%d-%d]\nm = drawn[t-%d]\n",MIN_V, MAX_V, MIN_K, MAX_K, MIN_T, MAX_T, MAX_M);
	printf("out = output file\n[in] = input file\n");
}

int checkArguments (int argc, char **argv, int *v, int *k, int *t, int *m, char **fileout, char **filein)
{
	// check number of arguments
	if (argc < 6 || argc > 7)
		return ERR_WRONG_NUMBER_ARGS;
	// check v
	if(sscanf_s(argv[1], "%d", v) != 1)
		return ERR_INVALID_V;
	if(*v < MIN_V || *v > MAX_V)
		return ERR_INVALID_V;
	// check k
	if(sscanf_s(argv[2], "%d", k) != 1)
		return ERR_INVALID_K;
	if(*k < MIN_K || *k > MAX_K)
		return ERR_INVALID_K;
	if(*k >= *v )
		return ERR_INVALID_VK;
	if(*k == MAX_K && *v > MED_V)
		return ERR_INVALID_COMB;
	// check t
	if(sscanf_s(argv[3], "%d", t) != 1)
		return ERR_INVALID_T;
	if(*t < MIN_T || *t > MAX_T)
		return ERR_INVALID_T;
	if(*t > *k )
		return ERR_INVALID_KT;
	// check m
	if(sscanf_s(argv[4], "%d", m) != 1)
		return ERR_INVALID_M;
	if(*m < *t || *m > MAX_M)
		return ERR_INVALID_M;
	if(*m > *k )
		return ERR_INVALID_KM;
	// output
	*fileout = argv[5];
	// input
	if (argc == 7)
		*filein = argv[6];
	return 0;
}

void main(int argc, char **argv)
{
	char *fileout = NULL;
	char *filein = NULL;

	int size; // guarda o total de volantes
	int newsize; // guarda o total de volantes apos a otimizacao
	int mov = 0; // guarda o total de mudancas conseguidas com sucesso
	int loop = 0; // guarda o numero de tentativas de otimizacao
	char ch; // para guardar o input do usuario (S/N)
	int LOOP_BREAK = 1000; // guarda o maximo de tentativas sem perguntar

	struct _timeb timebuffer1;
	struct _timeb timebuffer2;
	char timeline[TIME_STRINGLEN];
	errno_t err;

	double elapsed_time;

	int errnum = checkArguments(argc, argv, &v, &k, &t, &m, &fileout, &filein);
	if (errnum)
	{
		printHelp(errnum);
		return;
	}

	_ftime_s( &timebuffer1 );
	err = ctime_s( timeline, TIME_STRINGLEN, &timebuffer1.time );
	if (err != 0)
	{
		printf("Invalid Arguments for ctime_s. Error Code: %d\n", err);
		return;
	}
	printf( "Comecou em  %.19s.%hu\n", timeline, timebuffer1.millitm);

	if(!Initialize (v,k,t,m))
	{
		printf("Memory allocation ERROR\n");
		Finalize();
		return;
	}

	// read file if supplied
	if(filein)
	{
		if (StartFromFile (filein))
		{
			printf("Error reading file %s\n",filein);
			Finalize();
			return;
		}

		// check to see if is complete
		if (IndexOf(ICover,MAX_COVER,0,Size) != -1)
			Roll();
	}
	else
		Roll ();

	size = CoverSize();

	_ftime_s( &timebuffer2 );
	err = ctime_s( timeline, TIME_STRINGLEN, &timebuffer2.time );
	if (err != 0)
	{
		printf("Invalid Arguments for ctime_s. Error Code: %d\n", err);
		Finalize();
		return;
	}
	printf("Terminou em %.19s.%hu\n", timeline, timebuffer2.millitm);

	elapsed_time = difftime( timebuffer2.time , timebuffer1.time  );
	printf("Duracao %6.0f segundos.\n", elapsed_time );
	printf("size of cover %d\n", size);
	
	// Inicio da Otimizacao
	_ftime_s( &timebuffer1 );
	err = ctime_s( timeline, TIME_STRINGLEN, &timebuffer1.time );
	if (err != 0)
	{
		printf("Invalid Arguments for ctime_s. Error Code: %d\n", err);
		Finalize();
		return;
	}
	printf("Otimizacao Comecou em  %.19s.%hu\n", timeline, timebuffer1.millitm);

	do
	{
		mov		+= Optimize();
		newsize =  CoverSize();
		// se o numero de volantes diminuiu ou estourou limite de tentativas
		if (newsize < size || loop > LOOP_BREAK )
		{
			// mostra resultado
			_ftime_s( &timebuffer2 );
			err = ctime_s( timeline, TIME_STRINGLEN, &timebuffer2.time );
			if (err != 0)
			{
				printf("Invalid Arguments for ctime_s. Error Code: %d\n", err);
				Finalize();
				return;
			}
			printf( "Otimizacao Terminou em %.19s.%hu\n", timeline, timebuffer2.millitm);

			elapsed_time = difftime( timebuffer2.time , timebuffer1.time  );
			printf("Duracao %6.0f segundos.\n", elapsed_time );
			printf( "Moves:%d. size of cover %d\n", mov, newsize);

			// zera contador de mudancas
			mov = 0;

            // se estourou limite de tentativas, pergunta se continua tentando
			if (loop > LOOP_BREAK) 
			{
				printf("Continua? (S/N) ");
				ch = _getch();
				ch = toupper( ch );
				_putch (ch);
				if(ch == 'N') break;
			}
			else
				// salva o arquivo para preserva o que já foi conseguido até aqui
				PrintCover(fileout);

			// nova tentativa
			_ftime_s( &timebuffer1 );
			err = ctime_s( timeline, TIME_STRINGLEN, &timebuffer1.time );
			if (err != 0)
			{
				printf("\nInvalid Arguments for ctime_s. Error Code: %d\n", err);
				Finalize();
				return;
			}
			printf("\nOtimizacao Comecou em  %.19s.%hu\n", timeline, timebuffer1.millitm);

			// novo tamanho é o conseguido pelo otimizador
			size = newsize;
			// zera contador de tentativas
			loop = 0;
		}
		loop++;
	} while(1);

	PrintCover(fileout);

	Finalize();

}