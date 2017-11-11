#include "bits/stdc++.h"
#define puba push_back
#define ff first
#define ss second
#define bend(_x) begin(_x), end(_x)
#define szof(_x) ((int) (_x).size())
#define TASK_NAME ""

using namespace std;
typedef long long ll;
typedef unsigned long long ull;
typedef pair<int, int> pii;
const int INF = 1e9 + 7;
const ull P = 239;

struct expression {
    expression *left, *right;
    string name;
    ull h;
    int sz;
    bool is_variable;
    expression() {
        left = right = NULL;
        h = 0;
        sz = 0;
    }
    virtual void print() {
        cerr << "(";
        if (left != NULL) {
            left->print();
        }
        cerr << name;
        if (right != NULL) {
            right->print();
        }
        cerr << ")";
    }
};

ull get_hash(string s) {
    ull ret = 0;
    for (char c : s) {
        ret = ret * P + c;
    }
    return ret;
}

vector<ull> arrp = {1};

ull get_pow(int num) {
    while (num >= szof(arrp)) {
        arrp.puba(arrp.back() * P);
    }
    return arrp[num];
}

struct binary_expression : expression {
    binary_expression(expression *_left, expression *_right, string _name) {
        left = _left;
        right = _right;
        name = _name;
        h = ((('(' * get_pow(left->sz) + left->h) * get_pow(szof(name)) + get_hash(name)) * get_pow(right->sz) + right->h) * P + ')';
        sz = left->sz + szof(name) + right->sz + 2;
        is_variable = false;
    }
};

struct disjunction : binary_expression {
    disjunction(expression *_left, expression *_right) : binary_expression(_left, _right, "|") {}
};

struct conjunction : binary_expression {
    conjunction(expression *_left, expression *_right) : binary_expression(_left, _right, "&") {}
};

struct implication : binary_expression {
    implication(expression *_left, expression *_right) : binary_expression(_left, _right, "->") {}
};

struct negation : expression {
    negation(expression *_right) {
        right = _right;
        left = NULL;
        name = "!";
        h = (get_hash("(!") * get_pow(right->sz) + right->h) * P + ')';
        sz = right->sz + 3;
        is_variable = false;
    }
};

struct variable : expression {
    variable(string _name) {
        left = right = NULL;
        name = _name;
        h = get_hash(name);
        sz = szof(name);
        is_variable = true;
    }
    void print() {
        cerr << name;
    }
};

namespace parser {
    string s;
    int pos;

    vector<string> operations = {"->", "|", "&"};

    expression* parse_unary();

    expression* parse_binary(int depth) {
        if (depth == 3) {
            return parse_unary();
        }
        vector<expression*> ret = {parse_binary(depth + 1)};
        while (true) {
            bool flag = true;
            for (int i = 0; i < szof(operations[depth]); ++i) {
                if (szof(s) <= pos + i || s[pos + i] != operations[depth][i]) {
                    flag = false;
                    break;
                }
            }
            if (!flag) {
                if (depth == 0) {
                    while (szof(ret) > 1) {
                        auto b = ret.back();
                        ret.pop_back();
                        ret.back() = new binary_expression(ret.back(), b, operations[depth]);
                    }
                    return ret.back();
                } else {
                    auto tmp = ret[0];
                    for (int i = 1; i < szof(ret); ++i) {
                        tmp = new binary_expression(tmp, ret[i], operations[depth]);
                    }
                    return tmp;
                }
            }
            pos += szof(operations[depth]);
            ret.puba(parse_binary(depth + 1));
        }
    }

    bool is_variable(char c) {
        return ('A' <= c && c <= 'Z') || ('0' <= c && c <= '9') || ('a' <= c && c <= 'z');
    }

    expression* parse_unary() {
        if (pos == szof(s)) {
            cerr << "Cannot parse expression" << endl;
            cerr << s << endl;
            exit(1);
        }
        if (s[pos] == '!') {
            ++pos;
            return new negation(parse_unary());
        }
        if (s[pos] == '(') {
            ++pos;
            auto tmp = parse_binary(0);
            if (pos == szof(s) || s[pos] != ')') {
                cerr << "Cannot parse expression" << endl;
                cerr << s << endl;
                exit(1);
            }
            ++pos;
            return tmp;
        }
        string var;
        while (pos < szof(s) && is_variable(s[pos])) {
            var += s[pos];
            ++pos;
        }
        return new variable(var);
    }

    bool is_space(char c) {
        return c <= 32;
    }
}

expression* parse(const string& expr) {
    parser::s.clear();
    for (char c : expr) {
        if (!parser::is_space(c)) {
            parser::s += c;
        }
    }
    parser::pos = 0;
    auto tmp = parser::parse_binary(0);
    if (parser::pos != szof(parser::s)) {
        cerr << "Cannot parse expression" << endl;
        cerr << parser::s << endl;
        exit(1);
    }
    return tmp;
}

string buf;

unordered_map<ull, int> proved, assump;
unordered_map<ull, vector<pair<ull, int>>> transit;
unordered_map<ull, pii> modus_ponens;

void mark_proved(expression* expr, int ind) {
    proved[expr->h] = ind;
    if (expr->name == "->") {
        if (proved.count(expr->left->h)) {
            modus_ponens[expr->right->h] = {proved[expr->left->h], ind};
        } else {
            transit[expr->left->h].puba({expr->right->h, ind});
        }
    }
    for (auto p : transit[expr->h]) {
        modus_ponens[p.ff] = {ind, p.ss};
    }
    transit.erase(expr->h);
}

vector<expression*> axioms = {
parse("a -> b -> a"),
parse("(a -> b) -> (a -> b -> c) -> (a -> c)"),
parse("a -> b -> a & b"),
parse("a & b -> a"),
parse("a & b -> b"),
parse("a -> a | b"),
parse("b -> a | b"),
parse("(a -> c) -> (b -> c) -> (a | b -> c)"),
parse("(a -> b) -> (a -> !b) -> !a"),
parse("!a -> a -> b"),
parse("!!a -> a")};

namespace scheme {
    unordered_map<ull, ull> have;
    bool dfs(expression* expr, expression* axiom) {
        if (axiom->is_variable) {
            if (!have.count(axiom->h)) {
                have[axiom->h] = expr->h;
                return true;
            } else {
                return have[axiom->h] == expr->h;
            }
        }
        if (axiom->name != expr->name) {
            return false;
        }
        if (axiom->name == "!") {
            return dfs(expr->right, axiom->right);
        }
        return dfs(expr->left, axiom->left) && dfs(expr->right, axiom->right);
    }
}

bool is_scheme(expression* expr, expression* axiom) {
    scheme::have.clear();
    return scheme::dfs(expr, axiom);
}

string strip(string s) {
    while (szof(s) && s.back() == ' ') {
        s.pop_back();
    }
    reverse(bend(s));
    while (szof(s) && s.back() == ' ') {
        s.pop_back();
    }
    reverse(bend(s));
    return s;
}

int main() {
    getline(cin, buf);
    
    vector<string> hyps;

    int from = 0;
    int pos = 0;
    string res;
    for (; pos < szof(buf); ++pos) {
        if (buf[pos] == ',') {
            string cur = "";
            for (int i = from; i < pos; ++i) {
                cur += buf[i];
            }
            hyps.puba(strip(cur));
            from = pos + 1;
        }
        if (pos + 1 < szof(buf) && buf[pos] == '|' && buf[pos + 1] == '-') {
            string cur = "";
            for (int i = from; i < pos; ++i) {
                cur += buf[i];
            }
            cur = strip(cur);
            if (szof(cur)) {
                hyps.puba(strip(cur));
            }
            for (int i = pos + 2; i < szof(buf); ++i) {
                res += buf[i];
            }
        }
    }

    for (int i = 0; i < szof(hyps); ++i) {
        assump[parse(hyps[i])->h] = i;
    }

    int c = 0;
    while (getline(cin, buf)) {
        cout << "(" << c + 1 << ") " << buf << " (";
        auto cur = parse(buf);
        if (assump.count(cur->h)) {
            cout << "Предп. " << assump[cur->h] + 1;
            mark_proved(cur, c);
        } else {
            bool flag = false;
            for (int i = 0; i < szof(axioms); ++i) {
                if (is_scheme(cur, axioms[i])) {
                    cout << "Сх. акс. " << i + 1;
                    mark_proved(cur, c);
                    flag = true;
                    break;
                }
            }
            if (!flag) {
                if (modus_ponens.count(cur->h)) {
                    auto tmp = modus_ponens[cur->h];
                    cout << "M.P. " << tmp.ff + 1 << ", " << tmp.ss + 1;
                    mark_proved(cur, c);
                    flag = true;
                }
            }
            if (!flag) {
                cout << "Не доказано";
            }
        }
        cout << ")\n";
        ++c;
    }
    
    #ifdef LOCAL
        cerr << "time: " << clock() << endl;
    #endif
    return 0;
}