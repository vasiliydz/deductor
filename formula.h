#define min(x, y) (x) < (y) ? (x) : (y)
#define max(x, y) (x) > (y) ? (x) : (y)

#define UNDEFINED 0
#define UNKNOWN 1
#define VARIABLE 2
#define IMPLICATION 3
#define NEGATION 4

#define is_letter(x) (((x) >= 'A' && (x) <= 'Z') || ((x) >= 'a' && (x) <= 'z'))
#define is_digit(x) ((x) >= '0' && (x) <= '9')
#define NOT_A_FORMULA puts("Записанное выражение не является формулой"); formulas_free(); varstr_free(); exit(1);

struct _formula {	// Ну это понятно что
	int type;
	struct _formula *arg1, *arg2;
	int var;
};	typedef struct _formula formula;
struct _varstr {
	char s[16];
}; typedef struct _varstr varstr;

struct _ded {						// Элемент списка вывода
	int num;
	formula * f;
	int type, targ1, targ2;
	struct _ded *next;
}; typedef struct _ded ded;

// Немножко про элемент списка:
// 1) Если эта строчка -- аксиома или лемма, то нужен номер аксиомы (леммы) и формулы в качестве аргументов
// 2) Если гипотеза, то нужна только формула в arg1
// 3) Если Modus ponens, то в качестве аргументов должны быть указатели на выводы: первый аргумент (A), второй (A -> B)
// 4) Если формула уже была доказана ранее, то аргумент -- сама эта формула


int alloc_formula_num, var_num, read_pointer;
char * str_formula;
formula * formula_array;
varstr * var_array;

int ded_lemma_flag, lemma_flag, help_flag;

formula ** hypoth;

formula *fA, *fB, *fC;	// Заполняются, когда формула успешно проверяется, является ли она аксиомой или леммой

// СПИСОК АКСИОМ
// 1) A -> (B -> A)
// 2) (A -> (B -> C)) -> ((A -> B) -> (A -> C))
// 3) (!B -> !A) -> ((!B -> A) -> B)

// СПИСОК ЛЕММ
// 1) A -> A
// 2) !!A -> A
// 3) A -> !!A
// 4) !A -> (A -> B)
// 5) (A -> B) -> ((B -> C) -> (A -> C))
// 6) (A -> B) -> (!B -> !A)
// 7) A -> (!B -> !(A -> B))
// 8) (!B -> A) -> ((B -> A) -> A)
// 9) (A -> (B -> C)) -> (B -> (A -> C))
//
// 

// КОМАНДЫ ДЛЯ РАБОТЫ С ФОРМУЛАМИ
void formulas_alloc(int n);					// Выделяет место под все формулы
void formulas_and_ded_free();				// Освобождает место, использованное для формул и выводов
formula *alloc_formula();					// Находит место для формулы
void remove_formula(formula * f);			// Удаляет формулу
int alloc_var();							// Находит место для названия переменной
formula * read_formula(char * s);			// Преобразовывает строку в формулу
void print_formula(formula * f);			// Печатает формулу
formula * copy_formula(formula * f);		// Копирует формулу в новое место
int cmp_formula(formula * f, formula * g);	// Сравнивает две формулы (именно формулы, а не определяемые ими функции)

int calc_formula(formula * f, int * vals);	// Вычисляет значение формулы на наборе значений переменных из массива vals
											// i-я переменная равна первому биту (1) i-го элемента массива

void set_usable_vars(formula * f, int * vals);	// Выставляет в массиве vals второй бит (2) i-го числа в единицу,
												// если i-я переменная присутствует в формуле
												// vals должен состоять ТОЛЬКО из нулей для корректного использования

int dumb_check(formula * f, int * vals);		// Делает проверку на тавтологичность тупым перебором значений переменных
												// Если формула не тавтологична и vals != NULL, то по указателю val
												// разместится набор значений переменных, на которых формула принимает значение 0
												// Массив vals должен состоять только из нулей либо vals == NULL

void dumb_ded(formula * f);
ded * _dumb_ded(formula * f, int * vals);
void print_ded(ded * d);
// КОМАНДЫ ДЛЯ РАБОТЫ СО СПИСКАМИ ВЫВОДА

ded * _ded_lemma(int n, formula * f1, formula * f2, formula * f3);
ded * expand_lemma(ded * d);
ded * _ded_axiom(int n, formula * f1, formula * f2, formula * f3);
formula * imp(formula * f, formula * g);
int is_axiom(int n, formula * f);
int is_lemma(int n, formula * f);
ded * _expand_ded_lemma(ded * d, int h);

ded * _nded(ded * d, int n);

ded * expand_lemma(ded * d);
ded * full_expand_lemma(ded * d);
