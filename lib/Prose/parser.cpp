/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 3 "Prose.y" /* yacc.c:339  */


#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include "../../include/klee/Interpreter.h"
#include "Prose.h"
#include "../../include/klee/ExecutionState.h"
#include "llvm/Support/CommandLine.h"
#include "helper.h"

void yyerror(char const *s);
int yylex(void);

void panic(const char *msg) {
	fputs(msg, stderr);
	putc('\n', stderr);
	abort();
}

extern bool asyncMode;
extern klee::Interpreter *theInterpreter;
extern int primArraySize;
extern bool nullReturnValue;
extern cl::opt<bool> InitFuncPtrs;
extern cl::opt<bool> ModelFuncWithInlineASM;
extern cl::opt<bool> SkipSingletonHavocing;
extern cl::opt<std::string> EntryPoint;
extern std::map<std::string, std::string> functionModeledBy;
extern std::map<std::string, std::set<unsigned> > havocArgs;
extern std::map<std::string, std::set<std::string> > enforceOrigPatternWExceptions;
extern std::map<std::string, std::vector<BoundAST> > fieldConstraintMap;
extern std::map<std::string, std::vector<BoundAST> > funcArgConstraintMap;
extern std::map<std::string, std::map<unsigned, unsigned> > typeSpecificArrayFieldSize;
extern std::map<std::string, std::map<unsigned, unsigned> > funcSpecificArrayFieldSize;
extern unsigned loopBound;
extern bool symbolizeInlineAssembly;
extern std::set<std::string> lazyInitSingles;
extern std::map<std::string, std::vector<std::string> > inferenceClue;


#line 109 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* In a future release of Bison, this section will be replaced
   by #include "parser.h".  */
#ifndef YY_YY_HOME_UFAD_TYAVUZ_DOCUMENTS_TOOLS_PROMPTCONC_PROMPTCONC_LIB_PROSE_PARSER_H_INCLUDED
# define YY_YY_HOME_UFAD_TYAVUZ_DOCUMENTS_TOOLS_PROMPTCONC_PROMPTCONC_LIB_PROSE_PARSER_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    ALLOC = 258,
    ARG = 259,
    ARGS = 260,
    ARGSIZE = 261,
    ARRAY = 262,
    ASM = 263,
    BOUND = 264,
    BY = 265,
    CONTINUE = 266,
    CONSTANT = 267,
    DATA = 268,
    DESTARG = 269,
    EMBEDS = 270,
    ENTRYPOINT = 271,
    EXCEPT = 272,
    FALSEVAL = 273,
    FIELD = 274,
    FREE = 275,
    FUNCPTRS = 276,
    FUNCS = 277,
    FUNCTION = 278,
    GLOBAL = 279,
    HAVOC = 280,
    HAVOCING = 281,
    IF = 282,
    IS = 283,
    INIT = 284,
    INITZERO = 285,
    INLINE = 286,
    INTEGER = 287,
    LIFECYCLE = 288,
    LOOP = 289,
    MEMARG = 290,
    MEMRETURN = 291,
    MODEL = 292,
    MODELS = 293,
    MODELED = 294,
    NULL_TOKEN = 295,
    OF = 296,
    OFF = 297,
    ON = 298,
    PATTERN = 299,
    LTS = 300,
    LEQS = 301,
    GTS = 302,
    GEQS = 303,
    EQS = 304,
    NOTS = 305,
    NEQS = 306,
    PLUSS = 307,
    MINUSS = 308,
    TIMESS = 309,
    RETURN = 310,
    RETURNONLY = 311,
    RETURNOF = 312,
    SETTINGS = 313,
    SINGLETON = 314,
    SINGLETONS = 315,
    SIZE = 316,
    SIZEARG = 317,
    SIZEOF = 318,
    SKIP = 319,
    SYMBOLIZE = 320,
    TO = 321,
    TRUEVAL = 322,
    TYPE = 323,
    VALUE = 324,
    WHERE = 325,
    WITH = 326,
    L_IDENT = 327
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

union YYSTYPE
{
#line 124 "Prose.y" /* yacc.c:355  */

	bool y_bool;
	int y_int;
	klee::Sequential *y_sequential;
	klee::Identifier *y_id;
        std::vector<klee::Identifier*> *y_id_list;
	ASTNode *y_ast;
	BoundAST *y_bound;
	std::map<std::string, Binding> *y_bind_map;
	std::pair<std::string, Binding> *y_bind_pair;
        std::set<std::string> *y_exception_set;
        std::set<unsigned> *y_number_list;
	Binding *y_bind;
	char *y_ident;
        Op op;

#line 239 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:355  */
};

typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif


extern YYSTYPE yylval;
extern YYLTYPE yylloc;
int yyparse (void);

#endif /* !YY_YY_HOME_UFAD_TYAVUZ_DOCUMENTS_TOOLS_PROMPTCONC_PROMPTCONC_LIB_PROSE_PARSER_H_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 270 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
             && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE) + sizeof (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  4
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   193

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  80
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  21
/* YYNRULES -- Number of rules.  */
#define YYNRULES  70
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  177

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   327

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      78,    79,     2,     2,    75,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    73,    74,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    76,     2,    77,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66,    67,    68,    69,    70,    71,    72
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   156,   156,   164,   165,   169,   170,   171,   172,   173,
     174,   188,   201,   202,   206,   207,   210,   212,   218,   219,
     223,   224,   225,   228,   240,   241,   244,   245,   246,   250,
     266,   286,   293,   297,   302,   308,   312,   318,   324,   325,
     329,   334,   338,   352,   357,   365,   437,   438,   439,   440,
     445,   449,   453,   458,   463,   468,   473,   478,   484,   489,
     494,   499,   505,   509,   516,   528,   532,   537,   540,   543,
     547
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "ALLOC", "ARG", "ARGS", "ARGSIZE",
  "ARRAY", "ASM", "BOUND", "BY", "CONTINUE", "CONSTANT", "DATA", "DESTARG",
  "EMBEDS", "ENTRYPOINT", "EXCEPT", "FALSEVAL", "FIELD", "FREE",
  "FUNCPTRS", "FUNCS", "FUNCTION", "GLOBAL", "HAVOC", "HAVOCING", "IF",
  "IS", "INIT", "INITZERO", "INLINE", "INTEGER", "LIFECYCLE", "LOOP",
  "MEMARG", "MEMRETURN", "MODEL", "MODELS", "MODELED", "NULL_TOKEN", "OF",
  "OFF", "ON", "PATTERN", "LTS", "LEQS", "GTS", "GEQS", "EQS", "NOTS",
  "NEQS", "PLUSS", "MINUSS", "TIMESS", "RETURN", "RETURNONLY", "RETURNOF",
  "SETTINGS", "SINGLETON", "SINGLETONS", "SIZE", "SIZEARG", "SIZEOF",
  "SKIP", "SYMBOLIZE", "TO", "TRUEVAL", "TYPE", "VALUE", "WHERE", "WITH",
  "L_IDENT", "':'", "';'", "','", "'['", "']'", "'('", "')'", "$accept",
  "API_model", "global_settings", "global_setting", "choice", "regexplist",
  "data_models", "data_model", "type_embedding", "function_models",
  "function_model", "numberList", "boolean", "lifecycle_model",
  "lifecycle_sequence", "lifecycle_entry", "bound_constraint",
  "expression", "bindings", "binding", "entity", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,   322,   323,   324,
     325,   326,   327,    58,    59,    44,    91,    93,    40,    41
};
# endif

#define YYPACT_NINF -125

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-125)))

#define YYTABLE_NINF -43

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -14,   -44,    16,   -51,  -125,  -125,     0,   -37,   -10,     6,
      23,    14,   -16,     7,    10,   -31,    17,   -25,    -6,    18,
     -20,   -22,     2,    47,  -125,  -125,  -125,    32,  -125,    65,
    -125,  -125,  -125,   -22,   -22,   -12,   -22,   -22,  -125,  -125,
      57,    28,    29,   -15,     5,  -125,  -125,  -125,    60,    39,
    -125,   115,  -125,  -125,   -15,   -15,  -125,  -125,   -15,    35,
    -125,    33,  -125,    72,    62,    90,    45,   -15,   -15,   -15,
     -15,   -15,   -15,   -15,   -15,   -15,    73,   125,    -2,    74,
    -125,    80,    80,    80,    80,    80,    80,    90,    90,    62,
      75,    76,    77,    78,   140,   114,    81,   113,    82,  -125,
    -125,   126,    83,  -125,  -125,    84,   -18,   120,   128,    88,
    -125,   147,  -125,    -4,    75,    91,    -9,   130,   132,  -125,
     -33,   -11,    93,    94,  -125,    95,    96,    11,  -125,  -125,
    -125,  -125,  -125,   104,   141,  -125,    98,   142,   100,    -7,
    -125,    99,  -125,  -125,   171,  -125,   157,   145,   146,    -9,
      -9,  -125,  -125,  -125,   152,   148,   109,   150,   151,  -125,
    -125,   149,   119,   108,   110,    -5,  -125,  -125,  -125,    -9,
      -9,  -125,  -125,   174,  -125,   158,  -125
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     0,     1,     3,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     4,     5,    18,     0,     8,     0,
      15,    14,     6,     0,     0,     0,     0,     0,    13,    12,
       0,     0,     0,     0,     0,    21,    20,     7,     9,     0,
      22,     0,    48,    46,     0,     0,    47,    49,     0,     0,
      19,     0,    24,     0,    50,    51,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    10,     0,     0,
      61,    55,    56,    57,    58,    59,    60,    52,    53,    54,
       0,     0,     0,     0,     0,     0,     0,     0,     0,    32,
      23,     0,    45,    62,    16,    11,     0,     0,     0,     0,
      27,     0,    25,     0,     0,     0,     0,     0,     0,    33,
       0,     0,     0,     0,    67,     0,     0,     0,    64,    63,
      17,    36,    35,     0,     0,    31,     0,     0,     0,    39,
       2,    37,    40,    26,     0,    69,     0,     0,     0,     0,
       0,    28,    34,    38,     0,     0,     0,     0,     0,    68,
      65,     0,     0,     0,     0,    42,    41,    70,    66,     0,
       0,    44,    43,     0,    29,     0,    30
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int8 yypgoto[] =
{
    -125,  -125,  -125,  -125,    41,  -125,  -125,  -125,  -125,  -125,
    -125,  -125,  -124,  -125,  -125,    36,   -78,    48,  -125,    79,
    -125
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     6,    15,    32,   105,    35,    44,    45,    78,
      98,   120,   133,   140,   141,   142,    46,    59,   102,   103,
     128
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      99,    92,   123,    52,   154,   138,   154,     7,   136,   131,
       1,    40,   116,     8,     3,   147,     4,    53,    93,   124,
      30,    31,     5,    94,    16,   161,   162,    18,    17,     9,
     148,    95,    19,    22,    10,    54,    20,    11,    55,    21,
      12,    23,   137,    24,   117,   173,   174,    41,    26,    25,
      28,    29,    56,   125,    96,    34,    42,    57,   132,   126,
      27,   139,    33,    58,    13,    14,    43,   -42,   127,   155,
      97,   155,    36,    37,    38,    39,    43,    47,    48,    60,
      67,    68,    69,    70,    71,   171,    72,    73,    74,    75,
      67,    68,    69,    70,    71,    49,    72,    73,    74,    75,
      50,    51,    64,    65,    61,    77,    66,    67,    68,    69,
      70,    71,    62,    72,    76,    81,    82,    83,    84,    85,
      86,    87,    88,    89,    80,    67,    68,    69,    70,    71,
      63,    72,    73,    74,    75,    67,    68,    69,    70,    71,
      79,    72,    91,    90,    75,   108,   100,   101,   104,   106,
     107,   109,   111,   110,   113,   118,   112,   122,   114,   115,
     119,   121,   134,   130,   135,   143,   144,   145,   146,   149,
     151,   150,   153,   156,   152,   157,   158,   159,   160,   163,
     164,   165,   167,   168,   170,   169,    43,   172,   175,     0,
     176,     0,   166,   129
};

static const yytype_int16 yycheck[] =
{
      78,     3,     6,    18,    11,    16,    11,     7,    41,    18,
      24,    23,    30,    13,    58,     4,     0,    32,    20,    23,
      42,    43,    73,    25,    61,   149,   150,    21,    38,    29,
      19,    33,     9,    26,    34,    50,    22,    37,    53,    55,
      40,    31,    75,    74,    62,   169,   170,    59,    73,    32,
      32,    71,    67,    57,    56,     8,    68,    72,    67,    63,
      66,    72,    60,    78,    64,    65,    78,    74,    72,    76,
      72,    76,    40,     8,    33,    34,    78,    36,    37,    74,
      45,    46,    47,    48,    49,   163,    51,    52,    53,    54,
      45,    46,    47,    48,    49,    38,    51,    52,    53,    54,
      72,    72,    54,    55,    44,    72,    58,    45,    46,    47,
      48,    49,    73,    51,    79,    67,    68,    69,    70,    71,
      72,    73,    74,    75,    79,    45,    46,    47,    48,    49,
      15,    51,    52,    53,    54,    45,    46,    47,    48,    49,
      68,    51,    17,    70,    54,     5,    72,    72,    72,    72,
      72,    37,    39,    72,    28,    35,    74,    10,    75,    75,
      32,    73,    32,    72,    32,    72,    72,    72,    72,    65,
      72,    30,    72,    74,    32,     4,    19,    32,    32,    27,
      32,    72,    32,    32,    65,    36,    78,    77,    14,    -1,
      32,    -1,   156,   114
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    24,    81,    58,     0,    73,    82,     7,    13,    29,
      34,    37,    40,    64,    65,    83,    61,    38,    21,     9,
      22,    55,    26,    31,    74,    32,    73,    66,    32,    71,
      42,    43,    84,    60,     8,    86,    40,     8,    84,    84,
      23,    59,    68,    78,    87,    88,    96,    84,    84,    38,
      72,    72,    18,    32,    50,    53,    67,    72,    78,    97,
      74,    44,    73,    15,    97,    97,    97,    45,    46,    47,
      48,    49,    51,    52,    53,    54,    79,    72,    89,    68,
      79,    97,    97,    97,    97,    97,    97,    97,    97,    97,
      70,    17,     3,    20,    25,    33,    56,    72,    90,    96,
      72,    72,    98,    99,    72,    85,    72,    72,     5,    37,
      72,    39,    74,    28,    75,    75,    30,    62,    35,    32,
      91,    73,    10,     6,    23,    57,    63,    72,   100,    99,
      72,    18,    67,    92,    32,    32,    41,    75,    16,    72,
      93,    94,    95,    72,    72,    72,    72,     4,    19,    65,
      30,    72,    32,    72,    11,    76,    74,     4,    19,    32,
      32,    92,    92,    27,    32,    72,    95,    32,    32,    36,
      65,    96,    77,    92,    92,    14,    32
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    80,    81,    82,    82,    83,    83,    83,    83,    83,
      83,    83,    83,    83,    84,    84,    85,    85,    86,    86,
      87,    87,    87,    88,    89,    89,    90,    90,    90,    90,
      90,    90,    90,    91,    91,    92,    92,    93,    93,    93,
      94,    94,    95,    95,    95,    96,    97,    97,    97,    97,
      97,    97,    97,    97,    97,    97,    97,    97,    97,    97,
      97,    97,    98,    98,    99,   100,   100,   100,   100,   100,
     100
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,    16,     0,     3,     3,     3,     5,     3,     5,
       7,     9,     4,     4,     1,     1,     1,     3,     0,     3,
       1,     1,     2,     5,     0,     3,     4,     2,     5,     8,
      10,     4,     1,     1,     3,     1,     1,     1,     2,     1,
       1,     3,     1,     4,     4,     5,     1,     1,     1,     1,
       2,     2,     3,     3,     3,     3,     3,     3,     3,     3,
       3,     3,     1,     3,     3,     3,     4,     1,     3,     2,
       4
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static unsigned
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  unsigned res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
 }

#  define YY_LOCATION_PRINT(File, Loc)          \
  yy_location_print_ (File, &(Loc))

# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, Location); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  YYUSE (yylocationp);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  YY_LOCATION_PRINT (yyoutput, *yylocationp);
  YYFPRINTF (yyoutput, ": ");
  yy_symbol_value_print (yyoutput, yytype, yyvaluep, yylocationp);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                       , &(yylsp[(yyi + 1) - (yynrhs)])                       );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, YYLTYPE *yylocationp)
{
  YYUSE (yyvaluep);
  YYUSE (yylocationp);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Location data for the lookahead symbol.  */
YYLTYPE yylloc
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.
       'yyls': related to locations.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    /* The location stack.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls;
    YYLTYPE *yylsp;

    /* The locations where the error started and ended.  */
    YYLTYPE yyerror_range[3];

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yylsp = yyls = yylsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  yylsp[0] = yylloc;
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yyls1, yysize * sizeof (*yylsp),
                    &yystacksize);

        yyls = yyls1;
        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
  *++yylsp = yylloc;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location.  */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 159 "Prose.y" /* yacc.c:1646  */
    {
                //ExecutionState::setLifeCycleModel($4);
           }
#line 1574 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 5:
#line 169 "Prose.y" /* yacc.c:1646  */
    { primArraySize = (yyvsp[0].y_int); }
#line 1580 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 6:
#line 170 "Prose.y" /* yacc.c:1646  */
    { nullReturnValue = (yyvsp[0].y_bool); }
#line 1586 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 7:
#line 171 "Prose.y" /* yacc.c:1646  */
    { InitFuncPtrs = (yyvsp[0].y_bool); }
#line 1592 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 8:
#line 172 "Prose.y" /* yacc.c:1646  */
    { loopBound = (yyvsp[0].y_int); }
#line 1598 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 9:
#line 173 "Prose.y" /* yacc.c:1646  */
    { ModelFuncWithInlineASM = (yyvsp[0].y_bool); }
#line 1604 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 10:
#line 175 "Prose.y" /* yacc.c:1646  */
    { 
          std::string pattern((yyvsp[0].y_ident));
          /*if (pattern[0] == '*' && pattern[pattern.size()-1] == '*') 
             pattern = pattern.substr(1,pattern.size()-2);
          else assert(0 &&  "but_pattern should start and end with an asterisk\n");*/
          ModelFuncWithInlineASM = (yyvsp[-2].y_bool); 
          assert(ModelFuncWithInlineASM && "Providing a pattern when NOT modeling functions with assembly does not have any affect!\n");
          if (enforceOrigPatternWExceptions.find(pattern) != 
                     enforceOrigPatternWExceptions.end())
             assert(0 && "Pattern defined twice for exceptional cases of inline assembly!\n");
          std::set<std::string> excp;
          enforceOrigPatternWExceptions[pattern] = excp;
        }
#line 1622 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 11:
#line 189 "Prose.y" /* yacc.c:1646  */
    { 
          std::string pattern((yyvsp[-2].y_ident));
          /*if (pattern[0] == '*' && pattern[pattern.size()-1] == '*') 
             pattern = pattern.substr(1,pattern.size()-2);
          else assert(0 &&  "but_pattern should start and end with an asterisk\n");*/
          ModelFuncWithInlineASM = (yyvsp[-4].y_bool);
          assert(ModelFuncWithInlineASM && "Providing a pattern when NOT modeling functions with assembly does not have any affect!\n");
          if (enforceOrigPatternWExceptions.find(pattern) !=
                     enforceOrigPatternWExceptions.end())
             assert(0 && "Pattern defined twice for exceptional cases of inline assembly!\n");
          enforceOrigPatternWExceptions[pattern] = *(yyvsp[0].y_exception_set);
        }
#line 1639 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 12:
#line 201 "Prose.y" /* yacc.c:1646  */
    { symbolizeInlineAssembly = (yyvsp[0].y_bool); }
#line 1645 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 13:
#line 202 "Prose.y" /* yacc.c:1646  */
    { SkipSingletonHavocing = (yyvsp[0].y_bool); }
#line 1651 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 14:
#line 206 "Prose.y" /* yacc.c:1646  */
    { (yyval.y_bool) = true; }
#line 1657 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 15:
#line 207 "Prose.y" /* yacc.c:1646  */
    { (yyval.y_bool) = false; }
#line 1663 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 16:
#line 211 "Prose.y" /* yacc.c:1646  */
    { std::string es { (yyvsp[0].y_ident) }; (yyval.y_exception_set) = new std::set<std::string>(); (yyval.y_exception_set)->insert(es); }
#line 1669 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 17:
#line 213 "Prose.y" /* yacc.c:1646  */
    { std::string es { (yyvsp[0].y_ident) }; (yyval.y_exception_set)->insert(es); }
#line 1675 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 20:
#line 223 "Prose.y" /* yacc.c:1646  */
    {}
#line 1681 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 21:
#line 224 "Prose.y" /* yacc.c:1646  */
    { }
#line 1687 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 22:
#line 225 "Prose.y" /* yacc.c:1646  */
    { std::string s((yyvsp[0].y_ident)); lazyInitSingles.insert(s); }
#line 1693 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 23:
#line 228 "Prose.y" /* yacc.c:1646  */
    {
	std::vector<std::string> inf;
        std::string embedding((yyvsp[-3].y_ident)), embedded((yyvsp[0].y_ident));
        embedding = "%struct." + embedding;
        embedded = "%struct." + embedded;  
	if (inferenceClue.find(embedded) != inferenceClue.end())
             inf = inferenceClue[embedded];
        inf.push_back(embedding);
        inferenceClue[embedded] = inf;
}
#line 1708 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 26:
#line 244 "Prose.y" /* yacc.c:1646  */
    { functionModeledBy[(yyvsp[-3].y_ident)] = (yyvsp[0].y_ident); }
#line 1714 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 27:
#line 245 "Prose.y" /* yacc.c:1646  */
    { APIHandler::addIgnoreHandler((yyvsp[0].y_ident)); }
#line 1720 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 28:
#line 246 "Prose.y" /* yacc.c:1646  */
    { 
            std::string f((yyvsp[0].y_ident)); 
            havocArgs[f] = *(yyvsp[-2].y_number_list); 
        }
#line 1729 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 29:
#line 252 "Prose.y" /* yacc.c:1646  */
    {
          std::vector<std::string> par;
          par.push_back((yyvsp[-6].y_ident));
          par.push_back(std::to_string((yyvsp[-4].y_int)));
          if ((yyvsp[-2].y_bool))
             par.push_back("true");
          else par.push_back("false");
          if ((yyvsp[0].y_bool))
             par.push_back("true");
          else par.push_back("false");
          par.push_back("true"); // returns the pointer to the allocated mem 
          APIAction *a = new APIAction("alloc",par,new AllocAPIHandler()); 
          APIHandler::addAction((yyvsp[-6].y_ident),a);
        }
#line 1748 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 30:
#line 268 "Prose.y" /* yacc.c:1646  */
    {
          std::vector<std::string> par;
          par.push_back((yyvsp[-8].y_ident));
          par.push_back("-1");
          if ((yyvsp[-6].y_bool))
             par.push_back("true");
          else par.push_back("false");
          if ((yyvsp[-4].y_bool))
             par.push_back("true");
          else par.push_back("false");
          if ((yyvsp[-2].y_bool))
             par.push_back("true");
          else par.push_back("false");
          par.push_back(std::to_string((yyvsp[0].y_int)));
          APIAction *a = new APIAction("alloc",par,new AllocAPIHandler());
          APIHandler::addAction((yyvsp[-8].y_ident),a);
          
        }
#line 1771 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 31:
#line 286 "Prose.y" /* yacc.c:1646  */
    { 
          std::vector<std::string> par;
          par.push_back((yyvsp[-2].y_ident));
          par.push_back(std::to_string((yyvsp[0].y_int)));
          APIAction *a = new APIAction("free", par, new FreeAPIHandler());
          APIHandler::addAction((yyvsp[-2].y_ident),a);
        }
#line 1783 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 32:
#line 293 "Prose.y" /* yacc.c:1646  */
    { }
#line 1789 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 33:
#line 297 "Prose.y" /* yacc.c:1646  */
    { 
		(yyval.y_number_list) = new std::set<unsigned>(); 
		assert((yyvsp[0].y_int) >= 0 && "Negative argument no!\n"); 
		(yyval.y_number_list)->insert((yyvsp[0].y_int)); 
	}
#line 1799 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 34:
#line 302 "Prose.y" /* yacc.c:1646  */
    { 
		assert((yyvsp[0].y_int) >= 0 && "Negative argument no!\n");
		(yyvsp[-2].y_number_list)->insert((yyvsp[0].y_int)); 
	}
#line 1808 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 35:
#line 308 "Prose.y" /* yacc.c:1646  */
    {
           (yyval.y_bool) = true;
         }
#line 1816 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 36:
#line 312 "Prose.y" /* yacc.c:1646  */
    {
           (yyval.y_bool) = false;
        }
#line 1824 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 37:
#line 318 "Prose.y" /* yacc.c:1646  */
    { 
            (yyval.y_sequential) = new Sequential();
            for(unsigned i=0; i<(yyvsp[0].y_id_list)->size(); i++)
               (yyval.y_sequential)->addStep((*(yyvsp[0].y_id_list))[i]);           
            ExecutionState::setLifeCycleModel((yyval.y_sequential)); 
        }
#line 1835 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 38:
#line 324 "Prose.y" /* yacc.c:1646  */
    { std::string ep { (yyvsp[0].y_ident) }; EntryPoint = ep; }
#line 1841 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 39:
#line 325 "Prose.y" /* yacc.c:1646  */
    { std::string ep { (yyvsp[0].y_ident) }; EntryPoint = ep; }
#line 1847 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 40:
#line 329 "Prose.y" /* yacc.c:1646  */
    { 
           (yyval.y_id_list) = new std::vector<Identifier*>(); 
           (yyval.y_id_list)->push_back((yyvsp[0].y_id));
           EntryPoint = (yyvsp[0].y_id)->getValue(); 
        }
#line 1857 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 41:
#line 334 "Prose.y" /* yacc.c:1646  */
    { (yyvsp[-2].y_id_list)->push_back((yyvsp[0].y_id)); (yyval.y_id_list) = (yyvsp[-2].y_id_list); }
#line 1863 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 42:
#line 338 "Prose.y" /* yacc.c:1646  */
    {
          std::string fname { (yyvsp[0].y_ident) };
          (yyval.y_id) = new Identifier(fname);
          ASTNode * n = new ConstantNode(1);
          Binding b;
          b.type = "func";
          b.comptype = "return";
          b.entity = fname;
          b.index = -1;
          BoundAST *bast = new BoundAST;
          bast->ast = n;
          bast->bindings[fname] = b; 
	  (yyval.y_id)->setSuccessConstraint(bast);
	}
#line 1882 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 43:
#line 352 "Prose.y" /* yacc.c:1646  */
    {
          std::string fname { (yyvsp[-3].y_ident) };
          (yyval.y_id) = new Identifier(fname);
          (yyval.y_id)->setSuccessReturnValue((yyvsp[-1].y_int));
        }
#line 1892 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 44:
#line 357 "Prose.y" /* yacc.c:1646  */
    {
          std::string fname { (yyvsp[-3].y_ident) };
          (yyval.y_id) = new Identifier(fname);
          (yyval.y_id)->setSuccessConstraint((yyvsp[0].y_bound));
        }
#line 1902 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 45:
#line 365 "Prose.y" /* yacc.c:1646  */
    {
		auto bindings = *(yyvsp[0].y_bind_map);
		delete (yyvsp[0].y_bind_map);
		(yyval.y_bound) = new BoundAST { (yyvsp[-3].y_ast), bindings };
                std::string entity = ""; std::string type = ""; std::string comptype = "";
                for(auto bi : bindings) {
                   if (entity == "" && bi.second.comptype != "funcname")
                      entity = bi.second.entity;
                   if (type == "")
                      type = bi.second.type;
                   else if (type != bi.second.type)
                      assert(0 && "Cannot mix field and function argument related constraints\n");
                   if (bi.second.comptype == "return")
                      comptype = bi.second.comptype;
                }
                std::vector<BoundAST> s;
                if (type == "type") {
                   if (fieldConstraintMap.find(entity) != fieldConstraintMap.end())
                      s = fieldConstraintMap[entity]; 
                   Binding bc; unsigned size;
                   if (isSizeOfConstant(*(yyval.y_bound), bc, size)) {
                      std::map<unsigned, unsigned>  m;
                      if (typeSpecificArrayFieldSize.find(bc.entity) != 
                                     typeSpecificArrayFieldSize.end())
                         m = typeSpecificArrayFieldSize[bc.entity];
                      m[bc.index] = size;
                      typeSpecificArrayFieldSize[bc.entity] = m;
                   }
                   else if (isSimpleEquality(*(yyval.y_bound))) {
                      // equality constraints will be applied first
                      s.insert(s.begin(), *(yyval.y_bound));
                      std::cerr << "Recorded simple equality for type " << entity << "\n";
                   }
                   else s.push_back(*(yyval.y_bound));
                   fieldConstraintMap[entity] = s;
                   std::cerr << "Storing a constraint for " << entity << "\n";
                   (yyval.y_bound)->ast->print();
                }
                else if (type == "func") {
                   if (comptype == "return") {
                      /*if (returnValueConstraintMap.find(entity) != returnValueConstraintMap.end())
                         s = returnValueConstraintMap[entity];
                      s.push_back(*$$);
                      returnValueConstraintMap[entity] = s;*/
                   }
                   else {
                      if (funcArgConstraintMap.find(entity) != funcArgConstraintMap.end())
                         s = funcArgConstraintMap[entity];
                      Binding bc; unsigned as; 
                      if (isArgSizeConstant(*(yyval.y_bound), bc, as)) {
                         std::map<unsigned, unsigned>  m;
                         if (funcSpecificArrayFieldSize.find(bc.entity) != 
                                           funcSpecificArrayFieldSize.end())
                            m = funcSpecificArrayFieldSize[bc.entity];
                         m[bc.index] = as;
                         funcSpecificArrayFieldSize[bc.entity] = m;
                      }
                      else if (isSimpleEquality(*(yyval.y_bound))) {
                         // equality constraints will be applied first
                         s.insert(s.begin(), *(yyval.y_bound));
                      }   
                      else s.push_back(*(yyval.y_bound));
                      funcArgConstraintMap[entity] = s;
                   }
                } 
                //std::cerr << "Generated constraint: \n";
                //$$->ast->print();	
                //std::cerr << "=============\n";
	}
#line 1976 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 46:
#line 437 "Prose.y" /* yacc.c:1646  */
    { (yyval.y_ast) = new ConstantNode((yyvsp[0].y_int)); }
#line 1982 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 47:
#line 438 "Prose.y" /* yacc.c:1646  */
    { (yyval.y_ast) = new ConstantNode(1); }
#line 1988 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 48:
#line 439 "Prose.y" /* yacc.c:1646  */
    { (yyval.y_ast) = new ConstantNode(0); }
#line 1994 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 49:
#line 440 "Prose.y" /* yacc.c:1646  */
    { 
             std::string id((yyvsp[0].y_ident)); 
             std::cerr << "identifier: " << id << "\n"; 
             (yyval.y_ast) = new IdentifierNode(id); 
        }
#line 2004 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 50:
#line 445 "Prose.y" /* yacc.c:1646  */
    { 
          (yyval.y_ast) = new ASTNode(NEG); 
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
        }
#line 2013 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 51:
#line 449 "Prose.y" /* yacc.c:1646  */
    { 
           (yyval.y_ast) = new ASTNode(MINUS);
           (yyval.y_ast)->addChild((yyvsp[0].y_ast));
        }
#line 2022 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 52:
#line 453 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(PLUS);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
	}
#line 2032 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 53:
#line 458 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(MINUS);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast)); 
	}
#line 2042 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 54:
#line 463 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(TIMES);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
	}
#line 2052 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 55:
#line 468 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(LT);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
	}
#line 2062 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 56:
#line 473 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(LTE);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
	}
#line 2072 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 57:
#line 478 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(GT);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
          std::cerr << "> exp\n";
	}
#line 2083 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 58:
#line 484 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(GTE);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
	}
#line 2093 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 59:
#line 489 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(EQ);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
	}
#line 2103 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 60:
#line 494 "Prose.y" /* yacc.c:1646  */
    {
          (yyval.y_ast) = new ASTNode(NEQ);
          (yyval.y_ast)->addChild((yyvsp[-2].y_ast));
          (yyval.y_ast)->addChild((yyvsp[0].y_ast));
	}
#line 2113 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 61:
#line 499 "Prose.y" /* yacc.c:1646  */
    { (yyval.y_ast) = (yyvsp[-1].y_ast); }
#line 2119 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 62:
#line 505 "Prose.y" /* yacc.c:1646  */
    {
		(yyval.y_bind_map) = new std::map<std::string, Binding> { *(yyvsp[0].y_bind_pair) };
		delete (yyvsp[0].y_bind_pair);
	}
#line 2128 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 63:
#line 509 "Prose.y" /* yacc.c:1646  */
    {
		(yyval.y_bind_map) = (yyvsp[-2].y_bind_map);
		(yyval.y_bind_map)->insert(*(yyvsp[0].y_bind_pair));
		delete (yyvsp[0].y_bind_pair);
	}
#line 2138 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 64:
#line 516 "Prose.y" /* yacc.c:1646  */
    {
                if ((yyvsp[0].y_bind)->type == "type" && (yyvsp[0].y_bind)->comptype == "funcname") {
                    std::string f((yyvsp[-2].y_ident));
                    (yyvsp[0].y_bind)->entity = f;
                    std::cerr << "Recorded " << f << " as a funcname binding\n";
                }
		(yyval.y_bind_pair) = new std::pair<std::string, Binding> { (yyvsp[-2].y_ident), *(yyvsp[0].y_bind) };
		delete (yyvsp[0].y_bind);
	}
#line 2152 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 65:
#line 528 "Prose.y" /* yacc.c:1646  */
    {
		// fieldConstraintMap
		(yyval.y_bind) = new Binding { "type", "none", (yyvsp[-2].y_ident), (unsigned int)(yyvsp[0].y_int) };
	}
#line 2161 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 66:
#line 532 "Prose.y" /* yacc.c:1646  */
    {
		// funcArgConstraintMap
		// entity: either a type or function name
		(yyval.y_bind) = new Binding { "type", "sizeof", (yyvsp[-2].y_ident), (unsigned int)(yyvsp[0].y_int) };
	}
#line 2171 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 67:
#line 537 "Prose.y" /* yacc.c:1646  */
    {
               (yyval.y_bind) = new Binding { "type", "funcname", "", (unsigned int)0 };
        }
#line 2179 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 68:
#line 540 "Prose.y" /* yacc.c:1646  */
    {
		(yyval.y_bind) = new Binding { "func", "none", (yyvsp[-2].y_ident), (unsigned int)(yyvsp[0].y_int) };
	}
#line 2187 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 69:
#line 543 "Prose.y" /* yacc.c:1646  */
    {
                std::string s((yyvsp[0].y_ident));
		(yyval.y_bind) = new Binding { "func", "return", s, 0 };
	}
#line 2196 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;

  case 70:
#line 547 "Prose.y" /* yacc.c:1646  */
    {
      		(yyval.y_bind) = new Binding { "func", "argsize", (yyvsp[-2].y_ident), (unsigned int)(yyvsp[0].y_int) };
        }
#line 2204 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
    break;


#line 2208 "/home/UFAD/tyavuz/Documents/tools/PROMPTConc/promptconc/lib/Prose/parser.cpp" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }

  yyerror_range[1] = yylloc;

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, &yylloc);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  yyerror_range[1] = yylsp[1-yylen];
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp, yylsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  /* Using YYLLOC is tempting, but would change the location of
     the lookahead.  YYLOC is available though.  */
  YYLLOC_DEFAULT (yyloc, yyerror_range, 2);
  *++yylsp = yyloc;

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp, yylsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 551 "Prose.y" /* yacc.c:1906  */

