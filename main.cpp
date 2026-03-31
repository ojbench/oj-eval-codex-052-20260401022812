#include <bits/stdc++.h>
using namespace std;

// We implement a symbolic engine for expressions over x with +,-,*,/, parentheses,
// and power forms x^n, sin^n x, cos^n x, as well as implicit multiplication like 3x^2sinx.
// Internal normal form is a fraction p/q where p and q are polynomials, and a polynomial
// is a sum of terms a * x^b * sin^c(x) * cos^d(x). We do not reduce fractions.

struct Term {
    long long a; // coefficient (non-zero for stored terms)
    int bx, bs, bc; // exponents for x, sin, cos (>=0)
    Term(long long a_=0,int bx_=0,int bs_=0,int bc_=0):a(a_),bx(bx_),bs(bs_),bc(bc_){}
};

static int cmpTerm(const Term& t1, const Term& t2){
    if(t1.bx!=t2.bx) return t1.bx>t2.bx? -1:1; // descending by x power
    if(t1.bs!=t2.bs) return t1.bs>t2.bs? -1:1;
    if(t1.bc!=t2.bc) return t1.bc>t2.bc? -1:1;
    return 0;
}

struct Poly {
    vector<Term> ts; // terms, keep zero-free and canonical order; combine like terms

    Poly(){}
    static Poly fromConstant(long long c){
        Poly p; if(c!=0) p.ts.push_back(Term(c,0,0,0)); return p;
    }
    static Poly fromTerm(const Term& t){ Poly p; if(t.a!=0) p.ts.push_back(t); return p; }

    void normalize(){
        // sort by powers and combine like terms
        sort(ts.begin(), ts.end(), [](const Term& x, const Term& y){
            if(x.bx!=y.bx) return x.bx>y.bx;
            if(x.bs!=y.bs) return x.bs>y.bs;
            return x.bc>y.bc;
        });
        vector<Term> v;
        for(auto &t: ts){
            if(t.a==0) continue;
            if(!v.empty() && v.back().bx==t.bx && v.back().bs==t.bs && v.back().bc==t.bc){
                v.back().a += t.a;
                if(v.back().a==0) v.pop_back();
            }else{
                v.push_back(t);
            }
        }
        ts.swap(v);
    }

    Poly operator+(const Poly& o) const{
        Poly r; r.ts.reserve(ts.size()+o.ts.size());
        r.ts = ts; r.ts.insert(r.ts.end(), o.ts.begin(), o.ts.end());
        r.normalize(); return r;
    }
    Poly operator-(const Poly& o) const{
        Poly r; r.ts = ts; for(auto t:o.ts){ r.ts.push_back(Term(-t.a,t.bx,t.bs,t.bc)); }
        r.normalize(); return r;
    }
    Poly mulTerm(const Term& m) const{
        if(m.a==0 || ts.empty()) return Poly();
        Poly r; r.ts.reserve(ts.size());
        for(const auto& t: ts){
            long long c = t.a * m.a;
            // Beware of overflow; limits are small by problem constraints
            r.ts.emplace_back(c, t.bx + m.bx, t.bs + m.bs, t.bc + m.bc);
        }
        r.normalize(); return r;
    }
    Poly operator*(const Poly& o) const{
        Poly r; for(const auto& t:o.ts){ r = r + this->mulTerm(t); } r.normalize(); return r;
    }

    Poly derivate() const{
        // d/dx of a*x^b * sin^c x * cos^d x
        // = a * [ b*x^{b-1} * sin^c * cos^d + c*x^b*sin^{c-1}*cos * cos^d + d*x^b*sin^c * (-sin) * cos^{d-1}]
        Poly r;
        for(const auto& t: ts){
            long long a = t.a;
            int b=t.bx,c=t.bs,d=t.bc;
            // part for x power
            if(b>0){ r.ts.emplace_back(a * b, b-1, c, d); }
            // part for sin power via chain rule: c*sin^{c-1}x * cos x
            if(c>0){ r.ts.emplace_back(a * c, b, c-1, d+1); }
            // part for cos power via chain rule: d*cos^{d-1}x * (-sin x)
            if(d>0){ r.ts.emplace_back(a * (-d), b, c+1, d-1); }
        }
        r.normalize(); return r;
    }

    bool isZero() const{ return ts.empty(); }
    string toString() const{
        if(ts.empty()) return "0";
        // Sort again to consistent order
        // Already normalized; but ensure stable concatenation where needed
        string s; bool first=true;
        for(const auto& t: ts){
            long long a=t.a; int b=t.bx, c=t.bs, d=t.bc;
            // Build factor string without sign
            string part;
            // coefficient magnitude
            long long mag = llabs(a);
            bool needCoef = true;
            if(b==0 && c==0 && d==0){
                // pure constant
                part += to_string(mag);
                needCoef = false; // already output the constant
            }else{
                if(mag!=1) part += to_string(mag);
                // x^b
                if(b>0){
                    if(!part.empty() && isdigit(part.back())) part += "x"; else part += "x";
                    if(b>1) { part += "^"; part += to_string(b); }
                }
                // sin^c x
                if(c>0){
                    part += "sin";
                    if(c>1){ part += "^"; part += to_string(c); }
                    part += "x";
                }
                // cos^d x
                if(d>0){
                    part += "cos";
                    if(d>1){ part += "^"; part += to_string(d); }
                    part += "x";
                }
                if(part.empty()) part = to_string(mag); // should not happen
            }

            // sign handling
            if(first){
                if(a<0) s += "-";
                s += part;
                first=false;
            }else{
                s += (a<0? "-":"+");
                s += part;
            }
        }
        return s;
    }
};

struct Frac{
    Poly p,q; // p/q
    Frac(){}
    Frac(const Poly& P, const Poly& Q):p(P),q(Q){}
    static Frac fromConstant(long long c){ return Frac(Poly::fromConstant(c), Poly::fromConstant(1)); }
    static Frac fromTerm(const Term& t){ return Frac(Poly::fromTerm(t), Poly::fromConstant(1)); }

    Frac operator+(const Frac& o) const{ return Frac(p*o.q + q*o.p, q*o.q); }
    Frac operator-(const Frac& o) const{ return Frac(p*o.q - q*o.p, q*o.q); }
    Frac operator*(const Frac& o) const{ return Frac(p*o.p, q*o.q); }
    Frac operator/(const Frac& o) const{ return Frac(p*o.q, q*o.p); }
    Frac derivate() const{ // (p/q)' = (p'*q - q'*p)/(q*q)
        Poly pp = p.derivate();
        Poly qp = q.derivate();
        return Frac(pp*q - qp*p, q*q);
    }
    string toString() const{
        string P = p.toString();
        string Q = q.toString();
        return string("(") + P + ")/(" + Q + ")";
    }
};

// Parser for the expression grammar.
// Grammar (implicit multiplication):
// expr := term { ('+'|'-') term }
// term := factor { factor }  // implicit multiplication of consecutive factors
// factor := signedFactor
// signedFactor := ['+'|'-']? primary
// primary := number | 'x' ['^' number]? | 'sin' ['^' number]? 'x' | 'cos' ['^' number]? 'x' | '(' expr ')' | fraction
// fraction: factor '/' factor  (but we parse with precedence: '/' and '*' have same left-associative? Problem defines expressions as via +,-,*,/ with parentheses. We implement left-assoc for * and /.)

struct Parser{
    const string s;
    int n; int i;
    Parser(const string& s_):s(s_),n((int)s_.size()),i(0){}

    void skip(){ while(i<n && isspace((unsigned char)s[i])) ++i; }
    bool match(char c){ skip(); if(i<n && s[i]==c){ ++i; return true;} return false; }
    bool peek(char c){ skip(); return i<n && s[i]==c; }
    bool startsWith(const string& t){ skip(); return s.compare(i,t.size(),t)==0; }
    long long parseInt(){ skip(); int sign=1; if(i<n && (s[i]=='+'||s[i]=='-')){ if(s[i]=='-') sign=-1; ++i; }
        long long val=0; bool any=false; while(i<n && isdigit((unsigned char)s[i])){ any=true; val=val*10 + (s[i]-'0'); ++i; }
        if(!any){ // treat standalone '+' or '-' as 1 or -1 when preceding variable? We'll only call parseInt when digits available.
            return sign; }
        return sign*val; }

    // We implement precedence: expr = addsub, where addsub uses + and - over muldiv terms.
    Frac parse();
    Frac parseExpr(){ Frac a = parseAddSub(); return a; }
    Frac parseAddSub(){ Frac a = parseMulDiv(); while(true){ skip(); if(i<n && (s[i]=='+'||s[i]=='-')){ char op=s[i++]; Frac b = parseMulDiv(); if(op=='+') a = a + b; else a = a - b; } else break; } return a; }
    Frac parseMulDiv(){ Frac a = parseFactor(); while(true){ skip(); if(i>=n) break; char c=s[i]; if(c=='+'||c=='-'||c==')') break; // end of term
            // implicit multiplication if next token starts a factor; '/' explicit
            if(c=='/') { ++i; Frac b = parseFactor(); a = a / b; }
            else { // multiplication (implicit or '*')
                if(c=='*'){ ++i; }
                Frac b = parseFactor(); a = a * b; }
        }
        return a; }

    Frac parseFactor(){ // optional sign chains
        skip(); int sign=1; while(i<n && (s[i]=='+'||s[i]=='-')){ if(s[i]=='-') sign*=-1; ++i; skip(); }
        Frac f = parsePrimary(); if(sign==-1){ f = Frac::fromConstant(-1) * f; } return f; }

    Frac parsePrimary(){ skip(); if(i>=n) return Frac::fromConstant(0);
        if(s[i]=='('){ ++i; Frac a = parseExpr(); if(!match(')')){} return a; }
        // number (possibly with implicit multiplication later handled by caller)
        if(isdigit((unsigned char)s[i])){
            long long v=0; while(i<n && isdigit((unsigned char)s[i])){ v = v*10 + (s[i]-'0'); ++i; }
            return Frac::fromConstant(v);
        }
        // x or x^n
        if(s[i]=='x'){
            ++i; int pow=1; if(match('^')){ // parse exponent
                long long e=0; bool any=false; bool neg=false; if(i<n && (s[i]=='+'||s[i]=='-')){ neg = (s[i]=='-'); ++i; }
                while(i<n && isdigit((unsigned char)s[i])){ any=true; e = e*10 + (s[i]-'0'); ++i; }
                if(neg) e = -e; pow = (int)e;
            }
            return Frac::fromTerm(Term(1, max(0,pow), 0, 0));
        }
        // sin^k x or sin x
        if(startsWith("sin")){
            i += 3; int pow=1; if(match('^')){ long long e=0; while(i<n && isdigit((unsigned char)s[i])){ e = e*10 + (s[i]-'0'); ++i; } pow=(int)e; }
            // must follow 'x'
            if(i<n && s[i]=='x') ++i; return Frac::fromTerm(Term(1,0,max(0,pow),0));
        }
        if(startsWith("cos")){
            i += 3; int pow=1; if(match('^')){ long long e=0; while(i<n && isdigit((unsigned char)s[i])){ e = e*10 + (s[i]-'0'); ++i; } pow=(int)e; }
            if(i<n && s[i]=='x') ++i; return Frac::fromTerm(Term(1,0,0,max(0,pow)));
        }
        // Unary '+' or '-' handled in factor
        // Fallback: treat unknown as 0
        return Frac::fromConstant(0);
    }
};

Frac Parser::parse(){ return parseExpr(); }

static string fracToOutput(const Frac& f){
    // Output p/q as strings, but per examples, if denominator is 1, print just polynomial string; else "(p)/(q)" but samples omit outer parentheses at top-level? The README's sample prints "(x-sinx+1)/(x-sinx)" without extra parentheses around numerator terms in product, but our Poly::toString already outputs without spaces.
    string P = f.p.toString();
    string Q = f.q.toString();
    if(Q=="1") return P;
    return string("(") + P + ")/(" + Q + ")";
}

int main(){
    ios::sync_with_stdio(false);
    cin.tie(nullptr);
    string str; if(!(cin>>str)) return 0;
    Parser parser(str);
    Frac f = parser.parse();
    Frac df = f.derivate();
    cout << fracToOutput(f) << "\n";
    cout << fracToOutput(df) << "\n";
    return 0;
}

