# Problem 052 - 求导自动机

**ACMOJ Problem ID**: 1714

## Table of Contents

- [Problem 052 - 求导自动机](#problem-052-求导自动机)
  - [Table of Contents](#table-of-contents)
  - [Introduction](#introduction)
    - [Background](#background)
  - [Assignment Description](#assignment-description)
    - [Grade Composition](#grade-composition)
  - [Assignment Requirements](#assignment-requirements)
    - [Input Format](#input-format)
    - [Output Format](#output-format)
    - [Samples](#samples)
    - [Data Constraints](#data-constraints)
  - [Per-Testcase Resource Limits](#per-testcase-resource-limits)
  - [Test Data](#test-data)
  - [Submission Requirements](#submission-requirements)
    - [OJ Git Repository Compilation Process](#oj-git-repository-compilation-process)
    - [Git Configuration Requirements](#git-configuration-requirements)
    - [Submission Guidelines](#submission-guidelines)
    - [Evaluation Notes](#evaluation-notes)
    - [Academic Integrity](#academic-integrity)

## Introduction

### Background

Build symbolic differentiation engine: parse mathematical expressions and compute derivatives. Handles polynomials, fractions, trig.

## Assignment Description

### Grade Composition

| Grading Component | Percentage |
| :--: | :--: |
| Pass **1714. 求导自动机** | 80% |
| Code Review | 20% |

Here are several points that need clarification:

- In the Code Review, we will **strictly examine your code style and repository organization structure, etc.**

- This assignment provides some sample data for testing, stored in the `/workspace/data/052/data_test/` directory. Note that these are not the test cases on the Online Judge. Passing all local test cases does not guarantee that you will pass the OJ tests.

- Besides the provided sample data, we also encourage you to design your own test data based on your program logic to assist debugging.

## Assignment Requirements

### Problem Description

Vexoben 是一个被数学分析和编译器折磨的孩子。

这天，他再也不想求导了。他要你帮他写一个求导自动机。

为了方便阐述，这里先给出几个简单的定义（和数学上的定义可能有所不同）：

1. 项：一个项是一个形如 $ax^b\sin^cx\cos^dx$ 的式子（$a \in \mathbb{Z},a\neq 0,b,c,d \in \mathbb{N} $）

2. 多项式： 一个多项式由若干个项通过加减运算得到

3. 分式： 若 $p(x)$ 与 $q(x)$ 为两个多项式，则称 $\frac{p(x)}{q(x)}$ 为一个分式

4. 表达式： 经若干个分式加减乘除得到的式子称为表达式（可以包含括号）

现在，Vexoben 会丢给你一个 **表达式** $f(x)$，你需要输出两个**分式** $g(x),h(x)$，使得 $f(x) = g(x)$，$f^{\prime}(x) = h(x)$

为保证答案的唯一性，我们做出如下规定：

1. 若 $f=\frac{p_1}{q_1}$ 和 $g=\frac{p_2}{q_2}$ 是两个分式，定义分式的加法 $f+g := \frac{p_1\times q_2+p_2\times q_1}{q_1\times q_2}$ 

2. 若 $f=\frac{p_1}{q_1}$ 和 $g=\frac{p_2}{q_2}$ 是两个分式，定义分式的减法 $f-g := \frac{p_1\times q_2-p_2\times q_1}{q_1\times q_2}$ 

3. 若 $f=\frac{p_1}{q_1}$ 和 $g=\frac{p_2}{q_2}$ 是两个分式，定义分式的乘法 $f\times g := \frac{p_1\times p_2}{q_1\times q_2}$ 

4. 若 $f=\frac{p_1}{q_1}$ 和 $g=\frac{p_2}{q_2}$ 是两个分式，定义分式的除法 $f/g := \frac{p_1\times q_2}{q_1\times p_2}$ 

这四种运算之后，不需要对分式的上下进行约分；为了使答案唯一，我们规定经过约分后的分式和原来的分式是不相等的。

例如，若要计算 $\frac{1+x}{x^2}+\frac{1}{x}$ ，令$p_1 = 1 + x, q_1 = x ^ 2, p_2 = 1, q_2 = x$， 根据分式的加法的定义：

$$\frac{1+x}{x^2}+\frac{1}{x} = \frac{p_1\times q_2+p_2\times q_1}{q_1\times q_2} = \frac{(1+x)\times x+1\times x^2}{x^2 \times x}=\frac{2x^2+x}{x^3}$$

$\displaystyle\frac{2x^2+x}{x^3}$ 就是最终答案，你不应该把它约分为 $\displaystyle\frac{2x+1}{x^2}$

下面给出求导的运算法则。这部分与数学上相同。

1. $C^{\prime} = 0$ ($C$是常数)，$(x^n)^{\prime}=nx^{n-1} (n \geq 1)$，$(\cos x)^{\prime} = -\sin x$，$(\sin x)^{\prime} = \cos x$
1. 若 $f$ 和 $g$ 是两个分式，定义加法求导法则 $(f+g)^{\prime} = f ^{\prime} + g^{\prime}$
1. 若 $f$ 和 $g$ 是两个分式，定义减法求导法则 $(f-g)^{\prime} = f ^{\prime} - g^{\prime}$
1. 若 $f$ 和 $g$ 是两个分式，定义乘法求导法则 $(f\times g)^{\prime} = f ^{\prime} \times g + g^{\prime} \times f$
1. 若 $f$ 和 $g$ 是两个分式，定义除法求导法则 $(f/g)^{\prime} = (f ^{\prime} \times g - g^{\prime} \times f) / (g \times g)$
1. 链式求导法则：$[f(g(x))]^{\prime} = f^{\prime}(g(x)) \times g^{\prime}(x)$ （如果你不理解这个公式，你只需要知道 $(\sin^nx)^{\prime} = n\sin^{n-1}x\cos x$ 和$(\cos^{n}x)^{\prime} = -n\sin x\cos^{n-1}x$ 就行了）

此外，我们规定，你需要先将表达式通过分式的四则运算转化为分式，再对分式进行求导。

例如，要计算 $\frac{\frac{1}{x}}{1+x}$ 的导数，令 $f = \frac{1}{x} $ 和 $g = \frac{1+x}{1}$ 为两个分式，根据分式的除法的定义：

$$\frac{f}{g} = \frac{1 \times 1}{x \times (x + 1)} = \frac{1}{x^2+x}$$

再运用除法求导法则，

$$\left(\frac{1}{x^2+x}\right)^{\prime} = \frac{0\times (x^2+x) - (2x + 1) \times  1}{(x^2+x)\times (x^2+x)} = \frac{-2x-1}{x^4+2x^3+x^2}$$

而不是直接运用除法求导法则：

$$\left(\frac{\frac{1}{x}}{1+x}\right)^{\prime} = \frac{f ^{\prime} \times g - g^{\prime} \times  f}{g \times  g} = \frac{-\frac{1+x}{x^2}-\frac{1}{x}}{(1+x)\times (1+x)} = \frac{\frac{-2x^2-x}{x^3}}{x^2+2x+1} = \frac{-2x^2-x}{x^5+2x^4+x^3}$$

请注意，虽然不用进行约分，但是合并同类项这一化简是需要进行的。例如 $\sin x + 2\sin x$ 应写为 $3\sin x$

另外，你不需要考虑诸如 $\sin^2x+\cos^2x = 1$ 的化简。换言之，你不用考虑除了本题给定公式之外的任何公式。

为保证答案的唯一性，你需要按照如下格式输出答案：

1. 答案应形为 $(s_1)/(s_2)$ 的形式，其中 $s_1$，$s_2$ 分别为分式的分子和分母。当 $s_1$ 的项数超过 $1$ 项时，应该保留 $s_1$ 外面的括号，否则不应添加括号，$s_2$ 同理；$s_1$ 与 $s_2$ 内部不应出现任何的除号与括号

2. $s_1$ 与 $s_2$ 内部应当是由加号或减号隔开的若干个项（但不应出现类似于 $x- -5$（$x$ 减去负 $5$）这样的写法，而应写成 $x+5$）。如果第一项的系数是正数，不应该带有符号。项的系数和字母之间不应该有乘号。如果项的系数绝对值为 $1$ 且该项不是常数项时，只需要保留符号。指数用符号 `^` 表达。如果某个指数为 $0$，应当省略掉指数和相应的符号；如果指数为 $1$，应当省略掉指数。项之间以项的 $x$ 上方指数，$\sin x$ 上方指数，$\cos x$ 上方指数为第一、第二、第三关键字降序排列。(如$\frac{-1\times x^{0}\sin^1x\cos^2x+3\times\sin^2x}{3x}$ 应当输出 `(3sin^2x-sinxcos^2x)/3x`

3. 特殊的，若 $s_1 = 0$，你只需要输出一个 $0$；若 $s_2=1$，你只需要输出一个 $s_1$，且不用在 $s_1$ 外面打上括号，无论 $s_1$ 有几项。

4. 你的输出不应该包含除数字，加、减、除号（不应该有乘号）、括号、三个标识符 (x、sinx、cosx) 和 ^ 之外的其他字符。

保证输入数据是一个合法的符合正常书写规范的表达式，并且不会出现除数字，加、减、乘、除号、括号、三个标识符 (x、sinx、cosx) 和 ^ 之外的其他字符。组成表达式的项的书写规范和输出格式中要求的相同。运算过程中所有数字不会超过 int 类型存储的范围。负号只会出现在第一个字符或左括号后的第一个字符（不会出现 $9/-6x$ 这样的数据，但可能出现 $9/(-6x)$）

请通过动态申请空间的方式完成代码。在程序结束后，你应当释放所有动态申请的内存。如果不使用动态申请空间，助教将会酌情扣分。

以下是可供参考的代码模板，也欢迎同学们自己完成全部代码。


```cpp
#include<iostream>
#include<algorithm>
#include<cstring>

class term { //项
 public:
    int a, b, c, d;

    term() {}
    term(int _a, int _b, int _c, int _d) { // 你可以用 term t(1, 2, 3, 4); 创建一个表示 x^2sin^3xcos^4x 的term
        a = _a; b = _b; c = _c; d = _d;
    }
    bool operator == (const term &obj) const { // 相等表示是同类项
        return b == obj.b && c == obj.c && d == obj.d;
    }
    bool operator != (const term &obj) const {
        return b != obj.b || c != obj.c || d != obj.d;
    }
};

class poly { //多项式
 public:
    int n;
    term *t;

    poly() {n = 0; t = NULL;}
    poly(int _n) { // 构造函数
        n = _n;
        t = new term[n];
    }
    poly(const poly &p) {
        n = p.n;
        t = new term[n];
        for (int i = 0; i < n; ++i) {
            t[i] = p.t[i];
        }
    }
    void simplify() { // 合并同类项 
        // todo
    }
    poly operator + (const poly &obj) const { // 对 poly 重载加法运算符
        poly ans(n + obj.n);
        for (int i = 0; i < n; ++i) ans.t[i] = t[i];
        for (int i = 0; i < obj.n; ++i) ans.t[i + n] = obj.t[i];
        ans.simplify();
        return ans;
    }
    poly operator - (const poly &obj) const { // 对 poly 重载减法运算符
        poly ans(n + obj.n);
        for (int i = 0; i < n; ++i) ans.t[i] = t[i];
        for (int i = 0; i < obj.n; ++i) {
            ans.t[i + n] = obj.t[i];
            ans.t[i + n].a *= -1;
        }
        ans.simplify();
        return ans;
    }
    poly operator * (const poly &obj) const { // 对 poly 重载乘法运算符
        // 重载后,你可以使用 c = a * b 来进行 poly类型的乘法
        // 为了避免 CE,你不应该对 a 和 b 中的任何数据做出改动
        // todo
    }
    poly& operator = (const poly &obj) {
        if (&obj == this) return *this;
        n = obj.n;
        if (t != NULL) delete []t;
        t = new term[n];
        for (int i = 0; i < n; ++i) {
            t[i] = obj.t[i];
        }
        return *this;
    }
    poly derivate() const {  // 注意,你需要以“只读模式”访问当前的poly,并返回一个求导后的poly
        // todo
    }
    ~poly() { // 析构函数,释放内存
        if (t != NULL) delete []t;
    }
};

class frac { //分式
 public:
    poly p, q;

    frac() {}
    frac(int x) {
        p = poly(1);
        p.t[0] = term(x, 0, 0, 0);
        q = poly(1);
        q.t[0] = term(1, 0, 0, 0);
    }
    frac(term _p) {
        q = poly(1);
        q.t[0] = term(1, 0, 0, 0);
        p = poly(1);
        p.t[0] = _p;
    }
    frac(poly _p, poly _q) : p(_p), q(_q) {}

    frac operator + (const frac &obj) const {
        return frac(p * obj.q + q * obj.p, q * obj.q); // p1/q1+p2/q2=(p1*q2+p2*q1)/(q1*q2)
    }
    frac operator - (const frac &obj) const {
        // todo
    }
    frac operator * (const frac &obj) const {
        // todo
    }
    frac operator / (const frac &obj) const {
        // todo
    }
    frac derivate() const { // 对分式求导
        // todo 
    }
    void output() {
        // todo
    }
};

void solve(char *s, int n) {
    // todo 
}

int main() {
    std::string str;
    std::cin >> str;
    int n = str.length();
    char *s = new char[n + 2]{0};
    for (int i = 0; i < n; ++i) s[i] = str[i];
    solve(s, n);
    delete []s;
    return 0;
}
```

### Input Format

一行一个字符串，表示要求导的表达式

### Output Format

第一行一个字符串，表示将表达式化简为分式后的结果

第二行一个字符串，表示表达式求导的结果

### Samples

#### Sample 1

**Input:**
```
##### 样例输入1
```python
-1+x+x^2+3x^3+sinx+cos^2x+sin^4x-5cos^8x
```
##### 样例输出1
```python
3x^3+x^2+x+sin^4x+sinx-5cos^8x+cos^2x-1
9x^2+2x+4sin^3xcosx+40sinxcos^7x-2sinxcosx+cosx+1
```
##### 样例输入2
```python
-xsinxcos^2x*x^3sinx
```
##### 样例输出2
```python
-x^4sin^2xcos^2x
2x^4sin^3xcosx-2x^4sinxcos^3x-4x^3sin^2xcos^2x
```
##### 样例输入3
```python
1/(1-1/(1-sinx+x))
```
##### 样例输出3
```python
(x-sinx+1)/(x-sinx)
(cosx-1)/(x^2-2xsinx+sin^2x)
```
```

### Data Constraints

对于 $100\\%$ 的数据，读入的表达式项的数目不超过 $50$，所有的 $|a|,b,c,d \leq 10$

|测试点编号  |\* 出现次数  |/ 出现次数|不出现括号|性质一|性质二|
| ------------ | ------------ | ------------ | ------------ | ------------ | ------------ |
|  1 |0| 0  |$\checkmark$   |$\checkmark$   |$\checkmark$   |
|  2 |0  |0   | $\checkmark$  |   |$\checkmark$   |
|  3 |0  | 0  |$\checkmark$   |   |   |
|   4|$\leq 50$  |0   |$\checkmark$   |$\checkmark$   |$\checkmark$   |
|5   |$\leq 50$   | 0  |$\checkmark$   |   |$\checkmark$   |
|6   |$\leq 50$   | 0  |$\checkmark$   |   |   |
|7   |$\leq 50$   |$\leq 50$   |$\checkmark$   |$\checkmark$   |$\checkmark$   |
|8   |$\leq 50$   |$\leq 50$   |$\checkmark$   |   |$\checkmark$   |
|9   |$\leq 50$   |$\leq 50$    |$\checkmark$   |   |   |
|10   |$\leq 50$   |$\leq 1$    |   |$\checkmark$   |$\checkmark$   |
| 11  |$\leq 50$   |$\leq 1$    |   |   |$\checkmark$   |
|12   |$\leq 50$   |$\leq 1$    |   |   |   |
|13   |$\leq 50$   |$\leq 1$    |   |$\checkmark$   |$\checkmark$   |
|14   |$\leq 50$   |$\leq 1$    |   |   |$\checkmark$   |
|15   | $\leq 50$  |$\leq 1$    |   |   |   |
|16   |$\leq 50 $  |$\leq 50$    |   |   |   |
|17   | $\leq 50 $ |$\leq 50$    |   |   |   |
|18   | $\leq 50 $  |$\leq 50$    |   |   |   |
|19   |$\leq 50 $   |$\leq 50$    |   |   |   |
| 20  |$\leq 50 $   |$\leq 50$    |   |   |   |

- 性质一：表达式中不出现三角函数

- 性质二：每一项的 $b,c,d$ 三个指数中至多有一个不为 $0$

## Per-Testcase Resource Limits

- **Time Limit (per test case)**: 5000 ms
- **Memory Limit (per test case)**: 256 MiB
- **Disk Usage**: No disk usage is permitted.

## Test Data

The test data for this problem is located at `/workspace/data/052/data_test/`.

## Submission Requirements

### OJ Git Repository Compilation Process

For Git compilation, we will first clone the repository using a command similar to:
```bash
git clone <repo_url> . --depth 1 --recurse-submodules --shallow-submodules --no-local
```

Then we check if there is a `CMakeLists.txt` file. If it exists, we run (if not, a warning message will be displayed):
```bash
cmake .
```

Finally, we check if there is any of `GNUmakefile`/`makefile`/`Makefile` (if cmake was run previously, this will be the generated Makefile). If it exists, we run (if not, a warning message will be displayed):
```bash
make
```

After this process is complete, we will use the `code` file in the project root directory as the compilation result.

A `CMakeLists.txt` file is provided in the project. You can use or modify it as needed. The local environment has gcc-13 and g++-13 available.

### Git Configuration Requirements

**IMPORTANT**: You must create a `.gitignore` file in your project root directory to avoid OJ evaluation conflicts.

The `.gitignore` file should include at least the following entries:

```gitignore
CMakeFiles/
CMakeCache.txt
```

### Submission Guidelines

- The submitted code must be able to compile successfully through the above compilation process
- The compiled executable file name must be `code`
- The program needs to be able to read data from standard input and write results to standard output
- Please ensure the code runs correctly within the given time and space limits
- **You must use C++ or C language** to implement this assignment

### Evaluation Notes

- The evaluation system will test your program using the provided test data
- The program output must exactly match the expected output (including format)
- Exceeding time or memory limits will be judged as the corresponding error type
- Please pay attention to the overall time performance of your code and the time complexity of each part of your algorithm.

### Academic Integrity

If any violations are found during evaluation or code review (including but not limited to using unconventional methods to pass test cases), your final score may be significantly reduced or become **0 points**.
