#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define min(x, y) (x) < (y) ? (x) : (y)
#define max(x, y) (x) > (y) ? (x) : (y)

#define UNDEFINED 0
#define UNKNOWN 1
#define VARIABLE 2
#define IMPLICATION 3
#define NEGATION 4

#define is_letter(x) (((x) >= 'A' && (x) <= 'Z') || ((x) >= 'a' && (x) <= 'z'))
#define is_digit(x) ((x) >= '0' && (x) <= '9')
#define NOT_A_FORMULA puts("Записанное выражение не является формулой"); error_end();
#define WRONG_INSTR puts("Инструкция по доказательству лемм содержит ошибку"); error_end();
#define PARSE_NUMB(n)	(n) = 0; \
						read_pointer++; \
						do { \
							(n) = 10 * (n) + (proves[read_pointer] - '0'); \
							read_pointer++; \
						} while (is_digit(proves[read_pointer]));

#define AXIOM 10
#define LEMMA 20
#define HYPOTHESIS 30
#define MODUS_PONENS 40
#define PROVED 50

#define PRINT_DED_NUM		
#define PRINT_AXIOM(n)		printf("  (Аксиома %d)\n", (n))
#define PRINT_LEMMA(n)		printf("  (Лемма %d)\n", (n))
#define PRINT_HYPOT			printf("  (Гипотеза)\n")
#define PRINT_MP(a, a_to_b)	printf("  (Modus ponens %d, %d)\n", (a), (a_to_b))
#define PRINT_PROVED		printf("  (Доказано)\n")

struct _formula {
	int type;
	struct _formula *arg1, *arg2;
	int var;
};	typedef struct _formula formula;
struct _varstr {
	char s[16];
}; typedef struct _varstr varstr;

int alloc_formula_num = 0, var_num = 0, read_pointer = 0;
char * str_formula;				// Для преобразования строки в формулу, отдельно для него память не выделяется
formula * formula_array[1024];	// 1024 * 1024
varstr var_array[1024];			// 1024
int ded_count = 1;

formula *fA, *fB, *fC;	// Заполняются, когда формула успешно проверяется, является ли она аксиомой или леммой

formula ** hypoth;
int hyp_num;

char proves[] = "\
L1 =f2tf1f1; a1f1f2f0; a2f1f2f1; md1d2; a1f1f1f0; md4d3;!\
\
L2 =f2nf1; a3f2f1f0; =f3d1; =f4nf2; a1f3f4f0; md1d2; =f5f3g;\
   =f6f3h; a2f4f5f6; md3d4; a1f4f2f0; md6d5; l1f2f0f0; =f7d8;\
   a1f7f4f0; md8d9; a2f4f7f1; md7d11; md10d12;!\
\
L3 =f2nf1; =f3nf2; =f4nf3; l2f2f0f0; a3f1f3f0; md1d2; =f5d3;\
   a1f5f1f0; md3d4; =f6f5g; a2f1f6f3; md5d6; a1f1f4f0; md8d7;!\
\
L4 =f3nf1; =h1f1; =h2f3; =f4nf2; h1; a1f1f4f0; md1d2; h2; a1f3f4f0;\
   md4d5; a3f1f2f0; md6d7; md3d8; eh1; eh2;!\
\
L5 =f4tf2f3; =f5tf1f2; =h1f1; =h2f4; =h3f5; h1; h3; md1d2; h2; md3d4;\
   eh1; eh2; eh3;!\
\
L6 =f3nf1; =f4nf2; =f5nf3; =f6tf1f2; =h1f4; =h2f6; h1; a1f4f5f0;\
   md1d2; a3f2f3f0; md3d4; l2f1f0f0; h2; l5f5f1f2; md6d8; md7d9;\
   md10d5; eh1; eh2;!\
\
L7 =h1f1; =f3tf1f2; l1f3f0f0; a2f3f1f2; md1d2; h1; a1f1f3f0; md4d5;\
   md6d3; l6f3f2f0; md7d8; eh1;!\
\
L8 =f3nf1; =f4nf2; =f5nf4; =f6tf2f1; =f7tf4f1; =h1f6; =h2f7;\
   h1; l6f2f1f0; md1d2; a3f2f1f0; md3d4; h2; l6f4f1f0; md6d7;\
   l5f3f5f2; md8d9; l2f2f0f0; md11d10; md12d5; eh1; eh2;!\
\
L9 =f4tf1f2; =f5tf2f3; =f6tf1f3; =f7tf1f5; =h1f7; h1; a2f1f2f3;\
   md1d2; a1f2f1f0; l5f2f4f6; md4d5; md3d6; eh1;!\
";

int only_lemma = 0; // Если на вход подана только лемма и её можно доказать с применением леммы о дедукции

struct _ded {
	int num;						// Заполняется при печати
	formula *f;
	void *arg1, *arg2, *arg3;
	int type, tnum;
	struct _ded *next;
}; typedef struct _ded ded;

int alloc_ded_num = 0;
ded * ded_array[1024];			// 1024 * 1024  Дедуцировать придётся много

int ded_lemma_flag = 1, lemma_flag = 9, help_flag = 0;
ded * d_final;					// Содержит последний шаг вывода при вызове соответствующих функций

void error_end();

void formulas_alloc(int n) {
	formula_array[n] = (formula*) calloc(1024, sizeof(formula));
	return;
}
void deds_alloc(int n) {
	ded_array[n] = (ded*) calloc(1024, sizeof(ded));
	return;
}
void formulas_and_ded_free() {
	int i;
	for (i = 0; formula_array[i] != NULL && i < 1024; i++) {
		free(formula_array[i]);
	}
	for (i = 0; ded_array[i] != NULL && i < 1024; i++) {
		free(ded_array[i]);
	}
	free(hypoth);
	return;
}
formula *alloc_formula() {
	formula * ret;
	if (formula_array[alloc_formula_num/1024] == NULL) {
		formulas_alloc(alloc_formula_num/1024);
	}
	while ((formula_array[alloc_formula_num/1024][alloc_formula_num % 1024]).type != UNDEFINED) {
		alloc_formula_num++;
		if (alloc_formula_num >= 1024*1024 - 1) {
			puts("Не хватает памяти. Попробуйте воспользоваться леммами для упрощённого вывода формул.");
			error_end();
		}
		if (formula_array[alloc_formula_num/1024] == NULL) {
			formulas_alloc(alloc_formula_num/1024);
		}
	}
	ret = (formula_array[alloc_formula_num/1024] + (alloc_formula_num % 1024));
	alloc_formula_num++;
	ret->type = UNKNOWN;
	ret->var = -1;
	return ret;
}
ded *alloc_ded() {
	ded * ret;
	if (ded_array[alloc_ded_num/1024] == NULL) {
		deds_alloc(alloc_ded_num/1024);
	}
	while ((ded_array[alloc_ded_num/1024][alloc_ded_num % 1024]).type != UNDEFINED) {
		alloc_ded_num++;
		if (alloc_ded_num >= 1024*1024 - 1) {
			puts("Не хватает памяти. Попробуйте воспользоваться леммами для упрощённого вывода формул.");
			error_end();
		}
		if (ded_array[alloc_ded_num/1024] == NULL) {
			deds_alloc(alloc_ded_num/1024);
		}
	}
	ret = (ded_array[alloc_ded_num/1024] + (alloc_ded_num % 1024));
	alloc_ded_num++;
	ret->type = UNKNOWN;
	return ret;
}
void remove_formula(formula * f) {
	if (f == NULL) {
		return;
	}
	int i = 0;
	if (f->arg1 != NULL) {
		remove_formula(f->arg1);
		f->arg1 = NULL;
	}
	if (f->arg2 != NULL) {
		remove_formula(f->arg2);
		f->arg2 = NULL;
	}
	f->type = UNDEFINED;
	f->var = -1;
	for (i = 0; i < 1024; i++) {
		if (f - formula_array[i] < 1024) {
			alloc_formula_num = min(alloc_formula_num, f - formula_array[i] + 1024 * i);
			i = 1024;
		} else if (i == 1024) {
			printf("Ошибка при удалении формулы: чё-то не так");
			error_end();
		}
	}
	return;
}
void remove_one_formula(formula * f) {
	if (f != NULL) {
		int i;
		f->arg1 = NULL;
		f->arg2 = NULL;
		f->type = UNDEFINED;
		f->var = -1;
		for (i = 0; i < 1024; i++) {
			if (f - formula_array[i] < 1024) {
				alloc_formula_num = min(alloc_formula_num, f - formula_array[i] + 1024 * i);
				i = 1024;
			} else if (i == 1024) {
				printf("Ошибка при удалении формулы: чё-то не так");
				error_end();
			}
		}
	}
}
void remove_ded(ded * d) {
	if (d == NULL) {
		return;
	}
	d->num = 0;
	d->f = NULL;
	d->arg1 = NULL;
	d->arg2 = NULL;
	d->arg3 = NULL;
	d->type = 0;
	d->tnum = 0;
	remove_ded(d->next);
	d->next = NULL;
	int i = 0;
	for (i = 0; i < 1024; i++) {
		if (d - ded_array[i] < 1024) {
			alloc_ded_num = min(alloc_ded_num, d - ded_array[i] + 1024 * i);
			i = 1024;
		} else if (i == 1024) {
			printf("Ошибка при удалении вывода: чё-то не так");
			error_end();
		}
	}
	return;
}
int alloc_var() {
	return var_num++;
}
formula * _read_formula(int bracket_level, int only_arg) {
	formula * ret = NULL;
	formula * arg = NULL;
	int var_reader = -1, i;
	while (str_formula[read_pointer] == ' ') {read_pointer++;}
	if (str_formula[read_pointer] == '(') {
		read_pointer++;
		arg = _read_formula(bracket_level+1, 0);
	}
	else if (str_formula[read_pointer] == '!') {
		arg = alloc_formula();
		
		arg->type = NEGATION;
		read_pointer++;
		arg->arg1 = _read_formula(bracket_level, 1);
	}
	else if (is_letter(str_formula[read_pointer])) {
		arg = alloc_formula();
		arg->type = VARIABLE;
		arg->var = alloc_var();
		var_reader = 0;
		do {
		var_array[arg->var].s[var_reader] = str_formula[read_pointer];
		var_reader++;
		read_pointer++;
		} while (is_letter(str_formula[read_pointer]) || is_digit(str_formula[read_pointer]));
		var_array[arg->var].s[var_reader] = '\0';
		var_reader = -1;
		for (i = 0; i < var_num-1; i++) {
			if (strcmp(var_array[i].s, var_array[arg->var].s) == 0) {
				arg->var = i;
				i = var_num;
				var_num--;
			}
		}
	} else {NOT_A_FORMULA}
	
	if (only_arg) {
		return arg;
	}
	
	while (str_formula[read_pointer] == ' ') {read_pointer++;}
	if (str_formula[read_pointer] == ')' && bracket_level > 0) {
		read_pointer++;
		return arg;
	}
	else if (str_formula[read_pointer] == '\0' && bracket_level == 0) {
		return arg;
	}
	else if (str_formula[read_pointer] == '-') {
		read_pointer++;
		if (str_formula[read_pointer] != '>') {NOT_A_FORMULA}
		ret = alloc_formula();
		ret->type = IMPLICATION;
		ret->arg1 = arg;
		read_pointer++;
		ret->arg2 = _read_formula(bracket_level, 1);
	} else {NOT_A_FORMULA}
	
	while (str_formula[read_pointer] == ' ') {read_pointer++;}
	if (str_formula[read_pointer] == ')' && bracket_level > 0) {
		read_pointer++;
		return ret;
	}
	else if (str_formula[read_pointer] == '\0' && bracket_level == 0) {
		return ret;
	} else {NOT_A_FORMULA}
	return ret;
}
formula * read_formula(char * s) {
	read_pointer = 0;
	str_formula = s;
	formula * ret = _read_formula(0, 0);
	return ret;
}
void print_formula(formula * f) {
	if (f == NULL) {
		fputs("Этой формулы не существует", stdout);
	}
	if (f->type == UNDEFINED || f->type == UNKNOWN) {
		fputs("Этой формулы не существует", stdout);
	} else if (f->type == VARIABLE) {
		fputs(var_array[f->var].s, stdout);
	} else if (f->type == NEGATION) {
		fputc('!', stdout);
		if (f->arg1->type == IMPLICATION) {
			fputc('(', stdout);
			print_formula(f->arg1);
			fputc(')', stdout);
		} else {
			print_formula(f->arg1);
		}
	} else if (f->type == IMPLICATION) {
		if (f->arg1->type == IMPLICATION) {
			fputc('(', stdout);
			print_formula(f->arg1);
			fputc(')', stdout);
		} else {
			print_formula(f->arg1);
		}
		fputs(" -> ", stdout);
		if (f->arg2->type == IMPLICATION) {
			fputc('(', stdout);
			print_formula(f->arg2);
			fputc(')', stdout);
		} else {
			print_formula(f->arg2);
		}
	}
}
formula * copy_formula(formula * f) {
	if (f == NULL) {
		return NULL;
	}
	formula * ret = alloc_formula();
	ret->type = f->type;
	ret->arg1 = copy_formula(f->arg1);
	ret->arg2 = copy_formula(f->arg2);
	ret->var = f->var;
	return ret;
}
int cmp_formula(formula * f, formula * g) {
	if (f == NULL || g == NULL) {
		puts("Нулевую формулу на сравнение подали");
		error_end();
		return 0;
	}
	if (f->type == UNDEFINED || f->type == UNKNOWN || g->type == UNDEFINED || g->type == UNKNOWN) {
		return 0;
	} else if (f->type != g->type) {
		return 0;
	} else if (f->type == VARIABLE) {
		return (f->var == g->var);
	} else if (f->type == NEGATION) {
		return cmp_formula(f->arg1, g->arg1);
	} else if (f->type == IMPLICATION) {
		return cmp_formula(f->arg1, g->arg1) && cmp_formula(f->arg2, g->arg2);
	}
	return 0;
}
int calc_formula(formula * f, int * vals) {
	int arg1, arg2;
	if (f->type == VARIABLE) {
		return (vals[f->var]) & 1;
	} else if (f->type == NEGATION) {
		arg1 = calc_formula(f->arg1, vals);
		if (arg1 == -1) {
			return -1;
		}
		return arg1 ? 0 : 1;
	} else if (f->type == IMPLICATION) {
		arg1 = calc_formula(f->arg1, vals);
		arg2 = calc_formula(f->arg2, vals);
		if (arg1 == -1 || arg2 == -1) {
			return -1;
		}
		return ((!arg1) || (arg2)) ? 1 : 0;
	}
	return -1;
}
void set_usable_vars(formula * f, int * vals) {
	if (f->type == IMPLICATION) {
		set_usable_vars(f->arg1, vals);
		set_usable_vars(f->arg2, vals);
	} else if (f->type == NEGATION) {
		set_usable_vars(f->arg1, vals);
	} else if (f->type == VARIABLE) {
		vals[f->var] = 2;
	}
}
int dumb_check(formula * f, int * vals) {
	int * val_set, *val_p;
	if (vals == NULL) {
		val_set = (int *) calloc(var_num, sizeof(int));
	} else {
		val_set = vals;
	}
	val_p = (int *) calloc(var_num, sizeof(int));
	int i, p = 0, stop = 0;
	set_usable_vars(f, val_set);
	for (i = 0; i < var_num; i++) {
		if (val_set[i] == 2) {
			val_p[p] = i;
			val_set[i] = 0;
			p++;
		}
	}
	while (!(stop & 2)) {
		if (calc_formula(f, val_set) == 0) {
			free(val_p);
			if (vals == NULL) {
				free(val_set);
			}
			return 0;
		}
		i = 0;
		stop = stop & (~1);
		while (!(stop & 1)) {
			val_set[val_p[i]]++;
			if (val_set[val_p[i]] == 2) {
				val_set[val_p[i]] = 0;
				i++;
			} else {
				stop = stop | 1;
			}
			if (i >= p) {
				stop = stop | 2;
			}
		}
	}
	free(val_p);
	if (vals == NULL) {
		free(val_set);
	}
	return 1;
}
ded * _find_final_ded(ded * d) {
	ded * ret = d;
	if (d == NULL) {
		return NULL;
	}
	while (ret->next != NULL) {
		ret = ret->next;
	}
	return ret;
}

formula * var(int n) {
	if (n >= var_num) {
		puts("В функцию var подано недопустимое значение");
		error_end();
	}
	formula * ret = alloc_formula();
	ret->type = VARIABLE;
	ret->var = n;
	return ret;
}
formula * imp(formula * f, formula * g) {
	if (f == NULL || g == NULL) {
		puts("В функцию imp подан ноль");
		error_end();
	}
	formula * ret = alloc_formula();
	ret->type = IMPLICATION;
	ret->arg1 = f;
	ret->arg2 = g;
	return ret;
}
formula * not(formula * f) {
	if (f == NULL) {
		puts("В функцию not подан ноль");
		error_end();
	}
	formula * ret = alloc_formula();
	ret->type = NEGATION;
	ret->arg1 = f;
	return ret;
}

ded * copy_ded(ded * from, ded * to) {
	if (to == NULL || from == NULL) {
		puts ("Ошибка: в copy_ded подан нулевой аргумент");
		error_end();
	}
	to->f = from->f;
	to->arg1 = from->arg1;
	to->arg2 = from->arg2;
	to->arg3 = from->arg3;
	to->type = from->type;
	to->tnum = from->tnum;
	to->next = from->next;
	return to;
}
ded * _ded_axiom(int n, formula * f1, formula * f2, formula * f3) {
	if (n > 3 || n < 0) {
		puts("Wrong argument _ded_axiom");
		error_end();
	}
	ded * ret = alloc_ded();
	ret->type = AXIOM;
	ret->arg1 = (void*) f1;
	ret->arg2 = (void*) f2;
	ret->tnum = n;
	switch(n) {
		case 1:
		ret->f = imp(f1, imp(f2, f1));
		break;
		
		case 2:
		ret->arg3 = (void*) f3;
		ret->f = imp(imp(f1, imp(f2, f3)), imp(imp(f1, f2), imp(f1, f3)));
		break;
		
		case 3:
		ret->f = imp(imp(not(f2), not(f1)), imp(imp(not(f2), f1), f2));
		break;
	}
	d_final = ret;
	return ret;
}
ded * _ded_lemma(int n, formula * f1, formula * f2, formula * f3) {
	if (n > 9 || n < 0) {
		puts("Wrong argument _ded_lemma");
		error_end();
	}
	ded * ret = alloc_ded();
	ret->type = LEMMA;
	ret->arg1 = (void*) f1;
	ret->tnum = n;
	switch(n) {
		case 1:
		ret->f = imp(f1, f1);
		break;
		
		case 2:
		ret->f = imp(not(not(f1)), f1);
		break;
		
		case 3:
		ret->f = imp(f1, not(not(f1)));
		break;
		
		case 4:
		ret->arg2 = f2;
		ret->f = imp(not(f1), imp(f1, f2));
		break;
		
		case 5:
		ret->arg2 = f2;
		ret->arg3 = f3;
		ret->f = imp(imp(f1, f2), imp(imp(f2, f3), imp(f1, f3)));
		break;
		
		case 6:
		ret->arg2 = f2;
		ret->f = imp(imp(f1, f2), imp(not(f2), not(f1)));
		break;
		
		case 7:
		ret->arg2 = f2;
		ret->f = imp(f1, imp(not(f2), not(imp(f1, f2))));
		break;
		
		case 8:
		ret->arg2 = f2;
		ret->f = imp(imp(not(f2), f1), imp(imp(f2, f1), f1));
		break;
		
		case 9:
		ret->arg2 = f2;
		ret->arg3 = f3;
		ret->f = imp(imp(f1, imp(f2, f3)), imp(f2, imp(f1, f3)));
		break;
	}
	d_final = ret;
	return ret;
}
ded * _ded_hypoth(int n) {
	if (hypoth == NULL) {
		puts("Гипотез нет _ded_hypoth");
		error_end();
	}
	if (hyp_num <= n) {
		puts("Нет такой гипотезы");
		error_end();
	}
	ded * ret = alloc_ded();
	ret->type = HYPOTHESIS;
	ret->tnum = n;
	ret->f = hypoth[n];
	d_final = ret;
	return ret;
}
ded * _ded_proved(formula * f) {
	if (f == NULL) {
		puts("Ошибка: в _ded_proved подан NULL");
		error_end();
	}
	ded * ret = alloc_ded();
	ret->type = PROVED;
	ret->f = f;
	d_final = ret;
	return ret;
}
ded * _ded_mp(ded * a, ded * a_to_b) {
	if (a == NULL || a_to_b == NULL) {
		puts("Ошибка, на модус поненс подан нулевой аргумент");
		error_end();
	} else if (a_to_b->f->type != IMPLICATION) {
		puts("Для modus ponens нужны другие аргументы");
		error_end();
	} else if (!cmp_formula(a->f, a_to_b->f->arg1)) {
		puts("Тут modus ponens неприменим ващет");
		error_end();
	}
	ded * ret = alloc_ded();
	ret->type = MODUS_PONENS;
	ret->f = ((formula*)(a_to_b->f))->arg2;
	ret->arg1 = (void *) a;
	ret->arg2 = (void *) a_to_b;
	d_final = ret;
	return ret;
}
ded * _print_ded(ded * d) {
	printf("%d)  ", ded_count);
	print_formula(d->f);
	switch(d->type) {
		case AXIOM:
		PRINT_AXIOM(d->tnum);
		break;
		
		case LEMMA:
		PRINT_LEMMA(d->tnum);
		break;
		
		case HYPOTHESIS:
		PRINT_HYPOT;
		break;
		
		case MODUS_PONENS:
		PRINT_MP(((ded*)(d->arg1))->num, ((ded*)(d->arg2))->num);
		break;
		
		case PROVED:
		PRINT_PROVED;
		break;
	}
	d->num = ded_count;
	ded_count++;
	return d->next;
}
void print_ded(ded * d) {
	ded_count = 1;
	while (d != NULL) {
		d = _print_ded(d);
	}
}
int is_axiom(int n, formula * f) {
	if (n > 3 || n < 0) {
		puts("Wrong argument is_axiom");
		error_end();
	}
	if (f == NULL) {
		puts("Wrong argument is_axiom");
		error_end();
	}
	if (f->type != IMPLICATION) {
		return 0;
	}
	if (f->arg2->type != IMPLICATION) {
		return 0;
	}
	switch (n) {
		case 1:	// 1) A -> (B -> A)
		if (cmp_formula(f->arg1, f->arg2->arg2)) {
			fA = f->arg1;
			fB = f->arg2->arg1;
			fC = NULL;
			return 1;
		}
		return 0;
		break;
		
		case 2:	// 2) (A -> (B -> C)) -> ((A -> B) -> (A -> C))
		if (f->arg1->type != IMPLICATION) {return 0;}
		if (f->arg1->arg2->type != IMPLICATION) {return 0;}
		if (f->arg2->arg1->type != IMPLICATION) {return 0;}
		if (f->arg2->arg2->type != IMPLICATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1, f->arg2->arg1->arg1)) {return 0;}
		if (!cmp_formula(f->arg1->arg1, f->arg2->arg2->arg1)) {return 0;}
		if (!cmp_formula(f->arg1->arg2->arg1, f->arg2->arg1->arg2)) {return 0;}
		if (!cmp_formula(f->arg1->arg2->arg2, f->arg2->arg2->arg2)) {return 0;}
		
		fA = f->arg1->arg1;
		fB = f->arg1->arg2->arg1;
		fC = f->arg1->arg2->arg2;
		return 1;
		break;
		
		case 3:	// 3) (!B -> !A) -> ((!B -> A) -> B)
		if (f->arg1->type != IMPLICATION) {return 0;}
		if (f->arg1->arg1->type != NEGATION) {return 0;}
		if (f->arg1->arg2->type != NEGATION) {return 0;}
		if (f->arg2->arg1->type != IMPLICATION) {return 0;}
		if (f->arg2->arg1->arg1->type != NEGATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1->arg1, f->arg2->arg2)) {return 0;}
		if (!cmp_formula(f->arg2->arg1->arg1->arg1, f->arg2->arg2)) {return 0;}
		if (!cmp_formula(f->arg1->arg2->arg1, f->arg2->arg1->arg2)) {return 0;}
		
		fA = f->arg1->arg2->arg1;
		fB = f->arg2->arg2;
		fC = NULL;
		return 1;
		break;
	}
	error_end();
	return 0;
}
int is_lemma(int n, formula * f) {
	if (n > 9 || n < 0) {
		puts("Wrong argument _ded_lemma");
		error_end();
	}
	if (f == NULL) {
		puts("Wrong argument _ded_lemma");
		error_end();
	}
	if (f->type != IMPLICATION) {
		return 0;
	}
	
	switch (n) {
		case 1:	// 1) A -> A
		if (cmp_formula(f->arg1, f->arg2)) {
			fA = f->arg1;
			fB = NULL;
			fC = NULL;
			return 1;
		}
		return 0;
		break;
		
		case 2:	// 2) !!A -> A
		if (f->arg1->type != NEGATION) {return 0;}
		if (f->arg1->arg1->type != NEGATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1->arg1, f->arg2)) {return 0;}
		fA = f->arg2;
		fB = NULL;
		fC = NULL;
		return 1;
		break;
		
		case 3:	// 3) A -> !!A
		if (f->arg2->type != NEGATION) {return 0;}
		if (f->arg2->arg1->type != NEGATION) {return 0;}
		if (!cmp_formula(f->arg2->arg1->arg1, f->arg1)) {return 0;}
		fA = f->arg1;
		fB = NULL;
		fC = NULL;
		return 1;
		break;
		
		case 4:	// 4) !A -> (A -> B)
		if (f->arg1->type != NEGATION) {return 0;}
		if (f->arg2->type != IMPLICATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1, f->arg2->arg1)) {return 0;}
		fA = f->arg1->arg1;
		fB = f->arg2->arg2;
		fC = NULL;
		return 1;
		break;
		
		
		case 5:	// 5) (A -> B) -> ((B -> C) -> (A -> C))
		if (f->arg1->type != IMPLICATION) {return 0;}
		if (f->arg2->type != IMPLICATION) {return 0;}
		if (f->arg2->arg1->type != IMPLICATION) {return 0;}
		if (f->arg2->arg2->type != IMPLICATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1, f->arg2->arg2->arg1)) {return 0;}
		if (!cmp_formula(f->arg1->arg2, f->arg2->arg1->arg1)) {return 0;}
		if (!cmp_formula(f->arg2->arg1->arg2, f->arg2->arg2->arg2)) {return 0;}
		fA = f->arg1->arg1;
		fB = f->arg1->arg2;
		fC = f->arg2->arg2->arg2;
		return 1;
		break;
		
		case 6:	// 6) (A -> B) -> (!B -> !A)
		if (f->arg1->type != IMPLICATION) {return 0;}
		if (f->arg2->type != IMPLICATION) {return 0;}
		if (f->arg2->arg1->type != NEGATION) {return 0;}
		if (f->arg2->arg2->type != NEGATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1, f->arg2->arg2->arg1)) {return 0;}
		if (!cmp_formula(f->arg1->arg2, f->arg2->arg1->arg1)) {return 0;}
		fA = f->arg1->arg1;
		fB = f->arg1->arg2;
		fC = NULL;
		return 1;
		break;
		
		case 7:	// 7) A -> (!B -> !(A -> B))
		if (f->arg2->type != IMPLICATION) {return 0;}
		if (f->arg2->arg1->type != NEGATION) {return 0;}
		if (f->arg2->arg2->type != NEGATION) {return 0;}
		if (f->arg2->arg2->arg1->type != IMPLICATION) {return 0;}
		if (!cmp_formula(f->arg1, f->arg2->arg2->arg1->arg1)) {return 0;}
		if (!cmp_formula(f->arg2->arg1->arg1, f->arg2->arg2->arg1->arg2)) {return 0;}
		fA = f->arg1;
		fB = f->arg2->arg1->arg1;
		fC = NULL;
		return 1;
		break;
		
		case 8:	// 8) (!B -> A) -> ((B -> A) -> A)
		if (f->arg1->type != IMPLICATION) {return 0;}
		if (f->arg2->type != IMPLICATION) {return 0;}
		if (f->arg1->arg1->type != NEGATION) {return 0;}
		if (f->arg2->arg1->type != IMPLICATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1->arg1, f->arg2->arg1->arg1)) {return 0;}
		if (!cmp_formula(f->arg1->arg2, f->arg2->arg2)) {return 0;}
		if (!cmp_formula(f->arg1->arg2, f->arg2->arg1->arg2)) {return 0;}
		fA = f->arg1->arg2;
		fB = f->arg1->arg1->arg1;
		fC = NULL;
		return 1;
		break;
		
		case 9:	// 9) (A -> (B -> C)) -> (B -> (A -> C))
		if (f->arg1->type != IMPLICATION) {return 0;}
		if (f->arg2->type != IMPLICATION) {return 0;}
		if (f->arg1->arg2->type != IMPLICATION) {return 0;}
		if (f->arg2->arg2->type != IMPLICATION) {return 0;}
		if (!cmp_formula(f->arg1->arg1, f->arg2->arg2->arg1)) {return 0;}
		if (!cmp_formula(f->arg1->arg2->arg1, f->arg2->arg1)) {return 0;}
		if (!cmp_formula(f->arg1->arg2->arg2, f->arg2->arg2->arg2)) {return 0;}
		fA = f->arg1->arg1;
		fB = f->arg2->arg1;
		fC = f->arg1->arg2->arg2;
		return 1;
		break;
	}
	error_end();
	return 0;
}
ded * _expand_ded_lemma(ded * d, int h) {	// Возвращает новый вывод
	ded * ret, * darg1, * darg2;
	int i;
	formula * f = imp(hypoth[h], d->f);
	for (i = 1; i <= 3; i++) {
		if (is_axiom(i, f)) {
			switch (i) {
				case 1:
				ret = _ded_axiom(1, f->arg1, f->arg2->arg1, NULL);
				break;
				
				case 2:
				ret = _ded_axiom(2, f->arg1->arg1, f->arg1->arg2->arg1, f->arg1->arg2->arg2);
				break;
				
				case 3:
				ret = _ded_axiom(3, f->arg2->arg1->arg2, f->arg2->arg2, NULL);
				break;
			}
			return ret;
		}
	}
	remove_one_formula(f);
	
	switch(d->type) {
		
		case AXIOM:
		ret = _ded_axiom(d->tnum, (formula *) d->arg1, (formula *) d->arg2, (formula *) d->arg3);
		ret->next = _ded_axiom(1, ret->f, hypoth[h], NULL);
		ret->next->next = _ded_mp(ret, ret->next);
		break;
		
		case LEMMA:
		ret = _ded_lemma(d->tnum, (formula *) d->arg1, (formula *) d->arg2, (formula *) d->arg3);
		ret->next = _ded_axiom(1, ret->f, hypoth[h], NULL);
		ret->next->next = _ded_mp(ret, ret->next);
		break;
		
		case HYPOTHESIS:
		if (d->tnum == h) {
			ret = _ded_lemma(1, hypoth[h], NULL, NULL);
		} else {
			ret = _ded_hypoth(d->tnum);
			ret->next = _ded_axiom(1, ret->f, hypoth[h], NULL);
			ret->next->next = _ded_mp(ret, ret->next);
		}
		break;
		
		case MODUS_PONENS:
		ret = _expand_ded_lemma((ded*) d->arg1, h);
		darg1 = d_final;	// h -> A
		darg1->next = _expand_ded_lemma((ded *) d->arg2, h);
		darg2 = d_final;	// h -> (A -> B)
		darg2->next = _ded_axiom(2, hypoth[h], darg1->f->arg2, darg2->f->arg2->arg2);
		darg2->next->next = _ded_mp(darg2, darg2->next);
		d_final->next = _ded_mp(darg1, darg2->next->next);
		break;
	}
	return ret; 
}
ded * _nded(ded * d, int n) {
	int i = 1;
	ded * ret = d;
	while (i < n) {
		if (ret == NULL) {
			puts("Ошибка в _nded");
			error_end();
		}
		ret = ret->next;
		i++;
	}
	return ret;
}
ded * expand_lemma(ded * d) {				// Возвращает новый вывод
	if (d == NULL) {
		error_end();
	}
	if (d->type != LEMMA || d->tnum > 9) {
		puts("Ошибка в expand_lemma");
		error_end();
	}
	ded *ret, *darg, **last;
	last = &ret;
	formula *farg[20];
	formula ** tmp_hyp = hypoth;
	hypoth = (formula **) calloc(10, sizeof(formula *));
	int hyp_num_tmp = hyp_num;
	hyp_num = 10;
	int n, i;
	int k[3];
	farg[1] = (formula *) (d->arg1);
	farg[2] = (formula *) (d->arg2);
	farg[3] = (formula *) (d->arg3);
	read_pointer = 0;
	while (proves[read_pointer] != 'L' || proves[read_pointer+1] != d->tnum + '0') {
		read_pointer++;
	}
	read_pointer += 2;
	while (proves[read_pointer] != '!') {
		while (proves[read_pointer] == ' ') {
			read_pointer++;
		}
		switch (proves[read_pointer]) {
			case '=':
			read_pointer++;
			if (proves[read_pointer] == 'f') {
				PARSE_NUMB(n);
				if (proves[read_pointer] == 't') {			// Следствие
					read_pointer++;
					for (i = 0; i < 2; i++) {
						if (proves[read_pointer] != 'f') {		// Читаем два аргумента
							WRONG_INSTR;
						}
						PARSE_NUMB(k[i]);
					}
					farg[n] = imp(farg[k[0]], farg[k[1]]);
					
				} else if (proves[read_pointer] == 'n') {	// Отрицание
					read_pointer++;
					if (proves[read_pointer] != 'f') {		// Читаем один аргумент
						WRONG_INSTR;
					}
					PARSE_NUMB(k[0]);
					farg[n] = not(farg[k[0]]);
				} else if (proves[read_pointer] == 'd') {
					PARSE_NUMB(k[0]);
					darg = _nded(ret, k[0]);
					farg[n] = darg->f;
				} else if (proves[read_pointer] == 'f') {
					PARSE_NUMB(k[0]);
					if (proves[read_pointer] == 'g') {
						farg[n] = (farg[k[0]])->arg1;
					} else if (proves[read_pointer] == 'h') {
						farg[n] = (farg[k[0]])->arg2;
					} else {
						WRONG_INSTR;
					}
					read_pointer++;
				}
			} else if (proves[read_pointer] == 'h') {
				PARSE_NUMB(n);
				if (proves[read_pointer] != 'f') {
					WRONG_INSTR;
				}
				PARSE_NUMB(k[0]);
				hypoth[n] = farg[k[0]];
			}
			break;
			
			case 'a':
			PARSE_NUMB(n);
			if (n < 1 || n > 3) {
				WRONG_INSTR;
			}
			for (i = 0; i < 3; i++) {
				if (proves[read_pointer] != 'f') {		// Читаем два аргумента
					WRONG_INSTR;
				}
				PARSE_NUMB(k[i]);
			}
			(*last) = _ded_axiom(n, farg[k[0]], farg[k[1]], farg[k[2]]);
			last = &((*last)->next);
			break;
			
			case 'l':
			PARSE_NUMB(n);
			if (n < 1 || n > 9) {
				WRONG_INSTR;
			}
			for (i = 0; i < 3; i++) {
				if (proves[read_pointer] != 'f') {		// Читаем два аргумента
					WRONG_INSTR;
				}
				PARSE_NUMB(k[i]);
			}
			(*last) = _ded_lemma(n, farg[k[0]], farg[k[1]], farg[k[2]]);
			last = &((*last)->next);
			break;
			
			case 'h':
			PARSE_NUMB(n);
			(*last) = _ded_hypoth(n);
			last = &((*last)->next);
			break;
			
			case 'm':
			read_pointer++;
			for (i = 0; i < 2; i++) {
				if (proves[read_pointer] != 'd') {
					WRONG_INSTR;
				}
				PARSE_NUMB(k[i]);
			}
			(*last) = _ded_mp(_nded(ret, k[0]), _nded(ret, k[1]));
			last = &((*last)->next);
			break;
			
			case 'e':
			read_pointer++;
			if (proves[read_pointer] != 'h') {
				WRONG_INSTR;
			}
			PARSE_NUMB(n);
			darg = _expand_ded_lemma(d_final, n);
			remove_ded(ret);
			ret = darg;
			last = &(d_final->next);
			break;
			
			default:
			WRONG_INSTR;
			break;
		}
		if (proves[read_pointer] != ';') {
			WRONG_INSTR;
		}
		read_pointer++;
	}
	free(hypoth);
	hypoth = tmp_hyp;
	hyp_num = hyp_num_tmp;
	return ret;
}
ded * full_expand_lemma(ded * d) {			// Делает подстановку прям в старый вывод
	if (d == NULL) {
		puts("В full_expand_lemma подан нулевой аргумент");
		error_end();
	}
	int flag = 1;
	ded *now, *tmp1, *tmp2, *prev;
	while (flag) {
		prev = NULL;
		now = d;
		flag = 0;
		while (now != NULL) {
			if (now->type == LEMMA && now->tnum > lemma_flag) {
				tmp1 = now->next;
				tmp2 = expand_lemma(now);
				copy_ded(d_final, now);
				now->next = tmp1;
				if (now->type == MODUS_PONENS) {
					if (((ded*)(d_final->arg1))->next == d_final) {
						((ded*)(now->arg1))->next = now;
					} else if (((ded*)(d_final->arg2))->next == d_final) {
						((ded*)(now->arg2))->next = now;
					} else {
						puts("Ошибка в full_expand_lemma");
						error_end();
					}
				}
				if (prev != NULL) {
					prev->next = tmp2;
				} else {
					d = tmp2;
				}
				flag = 1;
			}
				prev = now;
				now = now->next;
		}
	}
	return d;
}

ded * _dumb_ded(formula * f, int * vals) {
	ded *d1, *d2, *tmp_final;
	int i;
	if (f == NULL) {
		puts("Вместо формулы тупому выводителю в _dumb_ded подано ничего");
		error_end();
	}
	if (f->type == IMPLICATION) {
		if (calc_formula(f->arg2, vals) == 1) {
			d1 = _dumb_ded(f->arg2, vals);
			tmp_final = d_final;
			d2 = _ded_axiom(1, f->arg2, f->arg1, NULL);
			tmp_final->next = d2;
			d2->next = _ded_mp(tmp_final, d2);
			return d1;
		} else if (calc_formula(f->arg1, vals) == 0) {
			d1 = _dumb_ded(f->arg1, vals);
			tmp_final = d_final;
			d2 = _ded_lemma(4, f->arg1, f->arg2, NULL);
			tmp_final->next = d2;
			d2->next = _ded_mp(tmp_final, d_final);
			return d1;
		} else {
			d1 = _dumb_ded(f->arg1, vals);
			tmp_final = d_final;
			d2 = _ded_lemma(7, f->arg1, f->arg2, NULL);
			tmp_final->next = d2;
			d2->next = _ded_mp(tmp_final, d_final);

			tmp_final = d_final;
			tmp_final->next = _dumb_ded(f->arg2, vals);
			tmp_final = d_final;
			tmp_final->next = _ded_mp(tmp_final, d2->next);
			return d1;
		}
	} else if (f->type == NEGATION) {
		if (calc_formula(f->arg1, vals) == 0) {
			return _dumb_ded(f->arg1, vals);
		} else {
			d1 = _dumb_ded(f->arg1, vals);
			tmp_final = d_final;
			d2 = _ded_lemma(3, f->arg1, NULL, NULL);
			tmp_final->next = d2;
			d2->next = _ded_mp(tmp_final, d_final);
			return d1;
		}
	} else if (f->type == VARIABLE) {
		d1 = _ded_hypoth(f->var);
		return d1;
	} else {
		puts("Чот ошибка");
		error_end();
		return NULL;
	}
}
void dumb_ded(formula * f) {
	int * val_set = (int *) calloc(var_num, sizeof(int));
	hyp_num = var_num;
	int i;
	if (dumb_check(f, val_set) == 0) {
		if (var_num == 1) {
			puts("Данная формула не является тавтологией, так как при значении переменной");
		} else {
			puts("Данная формула не является тавтологией, так как при значениях переменной");
		}
		for (i = 0; i < var_num; i++) {
			printf("%s = %d\n", var_array[i].s, val_set[i]);
		}
		if (calc_formula(f, val_set) == 0) {
			printf("Формула принимает значение 0\n");
		} else {
			puts("А, не, нормально всё на этом наборе");
		}
		return;
	}
	for (i = 0; i < var_num; i++) {
		val_set[i] = 0;
	}
	int stop = 0;
	ded * d;
	formula * g = copy_formula(f);
	formula ** hyp_var = (formula **) malloc(var_num * sizeof(formula*));
	for (i = 0; i < var_num; i++) {		// Делаем формулы вида !x_i
		hyp_var[i] = not(var(i));
	}
	hypoth = (formula **) malloc(var_num * sizeof(formula*));
										// Если можно пользоваться леммой о дедукции
	if (ded_lemma_flag == 1) {			// То это очень здорово, конечно	
		while (!(stop & 2)) {
			for (i = 0; i < var_num; i++) {
				if (val_set[i] == 0) {
					hypoth[i] = hyp_var[i];
				} else {
					hypoth[i] = hyp_var[i]->arg1;
				}
			}

			puts("Приведём вывод:");
			for (i = 0; i < var_num; i++) {
				print_formula(hypoth[i]);
				putchar(' ');
			}
			fputs("  |-   ", stdout);
			print_formula(g);
			printf("\n\n");
			d = _dumb_ded(g, val_set);
			d = full_expand_lemma(d);
			print_ded(d);
			remove_ded(d);
			if ((var_num / 10) % 10 != 1 && var_num % 10 >= 2 && var_num % 10 <= 4) { 
				printf("\nПрименим %d раза лемму о дедукции, тем самым доказана выводимость формулы\n", var_num);
			} else {
				printf("\nПрименим %d раз лемму о дедукции, тем самым доказана выводимость формулы\n", var_num);
			}
			formula * proved = g;
			for (i = var_num - 1; i >= 0; i--) {
				proved = imp(hypoth[i], proved);
			}
			print_formula(proved);
			printf("\n\n\n");
			for (i = 0; val_set[i] == 1; i++) {
				formula * tmp = proved;
				proved = proved->arg2;
				remove_one_formula(tmp);
				puts("Приведём вывод формулы");
				print_formula(proved);
				printf("\n\n");
				ded * tmp_final;
				tmp = imp(hyp_var[i], proved);
				d = _ded_proved(tmp);
				tmp = imp(hyp_var[i]->arg1, proved);
				d->next = _ded_proved(tmp);
				d->next->next = _ded_lemma(8, proved, hyp_var[i]->arg1, NULL);
				d->next->next->next = _ded_mp(d, d_final);
				d_final->next = _ded_mp(d->next, d->next->next->next);
				d = full_expand_lemma(d);
				print_ded(d);
				remove_ded(d);
				printf("\n\n\n");
			}
			i = 0;
			stop = stop & (~1);
			while (!(stop & 1)) {
				val_set[i]++;
				if (val_set[i] == 2) {
					val_set[i] = 0;
					i++;
				} else {
					stop = stop | 1;
				}
				if (i >= var_num) {
					stop = stop | 2;
				}
			}
			
		}
								// А если нельзя... но очень хочется, то можно
								// Можно просто скрыть использование леммы о дедукции от глаз пользователя
	} else {					// Он и не узнает
		ded ** dproved_stack = (ded **) malloc((var_num + 1) * sizeof(ded*));
		int now_stack = -1;
		ded * d1, * d2, * d3;
		while (!(stop & 2)) {
			for (i = 0; i < var_num; i++) {
				if (val_set[i] == 0) {
					hypoth[i] = hyp_var[i];
				} else {
					hypoth[i] = hyp_var[i]->arg1;
				}
			}
			d1 = _dumb_ded(g, val_set);
			for (i = var_num-1; i >= 0; i--) {
				d2 = _expand_ded_lemma(d_final, i);
				remove_ded(d1);
				d1 = d2;
			}
			now_stack++;
			dproved_stack[now_stack] = d1;
			for (i = 0; val_set[i] == 1; i++) {
				d1 = _find_final_ded(dproved_stack[now_stack-1]);
				d2 = _find_final_ded(dproved_stack[now_stack]);
				d1->next = dproved_stack[now_stack];
				d2->next = _ded_lemma(8, d2->f->arg2, d2->f->arg1, NULL);
				d2->next->next = _ded_mp(d1, d_final);
				d_final->next = _ded_mp(d2, d2->next->next);
				now_stack--;
			}
			i = 0;
			stop = stop & (~1);
			while (!(stop & 1)) {
				val_set[i]++;
				if (val_set[i] == 2) {
					val_set[i] = 0;
					i++;
				} else {
					stop = stop | 1;
				}
				if (i >= var_num) {
					stop = stop | 2;
				}
			}
		}
		dproved_stack[0] = full_expand_lemma(dproved_stack[0]);
		print_ded(dproved_stack[0]);
		free(dproved_stack);
	}
	free(val_set);
	free(hyp_var);
	free(hypoth);
	hypoth = NULL;
	return;
}

void error_end() {
	formulas_and_ded_free();
	exit(-1);
}
