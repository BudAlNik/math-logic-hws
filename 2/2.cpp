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
const ull P = 5237;

struct expression {
    expression *left, *right;
    string name;
    ull h;
    int sz;
    bool is_variable;
    set<ull> free_vars;
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
    virtual string get_s() {
        return "(" + left->get_s() + name + right->get_s() + ")";
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
        for (auto num : left->free_vars) {
            free_vars.insert(num);
        }
        for (auto num : right->free_vars) {
            free_vars.insert(num);
        }
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

struct unary_expression : expression {
    unary_expression(string _name, expression *_right) {
        right = _right;
        left = NULL;
        for (auto num : right->free_vars) {
            free_vars.insert(num);
        }
        name = _name;
        h = (get_hash("(" + _name) * get_pow(right->sz) + right->h) * P + ')';
        sz = right->sz + 2 + szof(name);
        is_variable = false;
    }

    unary_expression(string _name, string var, expression *_right) : unary_expression(_name + var, _right) {}

    string get_s() {
        return "(" + name + right->get_s() + ")";
    }
};

struct negation : unary_expression {
    negation(expression *_right) : unary_expression("!", _right) {}
};

struct variable : expression {
    variable(string _name) {
        left = right = NULL;
        name = _name;
        h = get_hash(name);
        sz = szof(name);
        is_variable = true;
        free_vars.insert(h);
    }
    void print() {
        cerr << name;
    }
    string get_s() {
        return name;
    }
};

struct any : binary_expression {
    any(string var, expression *_right) : binary_expression(new variable(var), _right, "@") {
        free_vars.erase(get_hash(var));
    }
    void print() {
        cerr << name;
        left->print();
        right->print();
    }
    string get_s() {
        return "@" + left->get_s() + right->get_s();
    }
};

struct exist : binary_expression {
    exist(string var, expression *_right) : binary_expression(new variable(var), _right, "?") {
        free_vars.erase(get_hash(var));
    }
    void print() {
        cerr << name;
        left->print();
        right->print();
    }
    string get_s() {
        return "?" + left->get_s() + right->get_s();
    }
};

/*
struct predicate : unary_expression {
    predicate(string _name, expression *_right) : unary_expression(_name, _right) {
        h = (get_hash(_name + "(") * get_pow(right->sz) + right->h) * P + ')';
        sz = right->sz + 2 + szof(name);
    }
    void print() {
        cerr << name << "(";
        right->print();
        cerr << ")";
    }
    string get_s() {
        return name + "(" + right->get_s() + ")";
    }
};
*/

struct func : unary_expression {
    func(string _name, expression *_right) : unary_expression(_name, _right) {
        h = (get_hash(_name + "(") * get_pow(right->sz) + right->h) * P + ')';
        sz = right->sz + 2 + szof(name);
    }
    void print() {
        cerr << name << "(";
        right->print();
        cerr << ")";
    }
    string get_s() {
        return name + "(" + right->get_s() + ")";
    }
};

struct increment : unary_expression {
    increment(expression *_right) : unary_expression("'", _right) {}
    void print() {
        right->print();
        cerr << "'";
    }
    string get_s() {
        return right->get_s() + "'";
    }
};

namespace parser {
    string s;
    int pos;

    vector<string> operations = {"->", "|", "&", "", "=", ",", "+", "*"};

    expression* parse_unary();
    expression* parse_unary2();

    expression* parse_binary(int depth) {
        if (depth == 3) {
            return parse_unary();
        }
        if (depth == szof(operations)) {
            return parse_unary2();
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
                if (operations[depth] == "->") {
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
        return ('0' <= c && c <= '9') || ('a' <= c && c <= 'z');
    }

    /*
    bool is_predicate(char c) {
        return ('0' <= c && c <= '9') || ('A' <= c && c <= 'Z');
    }
    */
    bool is_function(char c) {
        return ('0' <= c && c <= '9') || ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
    }

    expression* parse_unary() {
        if (pos == szof(s)) {
            cerr << "Cannot parse expression" << endl;
            cerr << "1" << endl;
            cerr << s << endl;
            exit(1);
        }
        if (s[pos] == '!') {
            ++pos;
            return new negation(parse_unary());
        } else if (s[pos] == '@') {
            ++pos;
            string tmp = "";
            while (pos < szof(s) && is_variable(s[pos])) {
                tmp += s[pos];
                ++pos;
            }
            return new any(tmp, parse_unary());
        } else if (s[pos] == '?') {
            ++pos;
            string tmp = "";
            while (pos < szof(s) && is_variable(s[pos])) {
                tmp += s[pos];
                ++pos;
            }
            return new exist(tmp, parse_unary());
        }

        /*
        if (s[pos] == '(') {
            ++pos;
            auto tmp = parse_binary(0);
            if (pos == szof(s) || s[pos] != ')') {
                cerr << "Cannot parse expression" << endl;
                cerr << s.substr(pos) << endl;
                cerr << "2" << endl;
                cerr << s << endl;
                exit(1);
            }
            ++pos;
            while (pos < szof(s) && s[pos] == '\'') {
                pos++;
                tmp = new increment(tmp);
            }
            return tmp;
        }
        */
        return parse_binary(4);
    }

    expression* parse_unary2() {
        if (pos == szof(s)) {
            cerr << "Cannot parse expression" << endl;
            cerr << "3" << endl;
            cerr << s << endl;
            exit(1);
        }
        if (is_function(s[pos])) {
            string tmp = "";
            while (pos < szof(s) && is_function(s[pos])) {
                tmp += s[pos];
                ++pos;
            }
            if (pos < szof(s) && s[pos] == '(') {
                ++pos;
                auto ret = new func(tmp, parse_binary(4));
                if (pos == szof(s) || s[pos] != ')') {
                    cerr << "Cannot parse expression" << endl;
                    cerr << "3.5" << endl;
                    cerr << s << endl;
                    exit(1);
                }
                ++pos;
                return ret;
            } else {
                expression* ret = new variable(tmp);
                while (pos < szof(s) && s[pos] == '\'') {
                    pos++;
                    ret = new increment(ret);
                }
                return ret;
            }
        }

        if (s[pos] == '(') {
            ++pos;
            auto tmp = parse_binary(0);
            if (pos == szof(s) || s[pos] != ')') {
                cerr << "Cannot parse expression" << endl;
                cerr << "4" << endl;
                cerr << s << endl;
                exit(1);
            }
            ++pos;
            while (pos < szof(s) && s[pos] == '\'') {
                pos++;
                tmp = new increment(tmp);
            }
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
        cerr << "5" << endl;
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
parse("!!a -> a"), 
parse("a = b -> a' = b'"), 
parse("a = b -> a = c -> b = c"), 
parse("a' = b' -> a = b"), 
parse("!a' = 0"), 
parse("a + b' = (a + b)'"), 
parse("a + 0 = a"), 
parse("a * 0 = 0"), 
parse("a * b' = a * b + a")};

string term;
bool flag_tied;

namespace scheme {
    unordered_map<ull, ull> have;
    bool dfs(expression* expr, expression* axiom) {
        if (expr == NULL && axiom == NULL) {
            return true;
        }
        if (axiom->is_variable) {
            if (axiom->name == "0") {
                return expr->name == "0";
            }
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
        return dfs(expr->left, axiom->left) && dfs(expr->right, axiom->right);
    }

    multiset<ull> tied;
    bool check_not_tied(expression* expr) {
        if (expr == NULL) {
            return true;
        }
        if (expr->is_variable) {
            return tied.find(expr->h) == tied.end();
        }
        return check_not_tied(expr->left) && check_not_tied(expr->right);
    }

    int dfs2(expression* expr, expression* expr0, string const& var) {
        if (expr == NULL && expr0 == NULL) {
            return true;
        }
        if (expr0->is_variable) {
            if (expr0->name == var && tied.find(expr0->h) == tied.end()) {
                if (!check_not_tied(expr)) {
                    term = expr->get_s();
                    flag_tied = true;
                }
                if (!have.count(expr0->h)) {
                    have[expr0->h] = expr->h;
                    return 1;
                } else {
                    return have[expr0->h] == expr->h;
                }
            }
        }
        if (expr0->name != expr->name) {
            return false;
        }
        if (expr->name == "@" || expr->name == "?") {
            tied.insert(expr->left->h);
            auto ret = dfs2(expr->right, expr0->right, var);
            tied.erase(tied.find(expr->left->h));
            return ret;
        }
        return dfs2(expr->left, expr0->left, var) && dfs2(expr->right, expr0->right, var);
    }
}

bool is_scheme(expression* expr, expression* axiom) {
    scheme::have.clear();
    flag_tied = false;
    return scheme::dfs(expr, axiom);
}

bool is_substitution(expression* expr, expression* expr0, string var) {
    scheme::have.clear();
    scheme::tied.clear();
    flag_tied = false;
    return scheme::dfs2(expr, expr0, var);
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

int cnt = 0;

void fail() {
    cout << "¬ывод некорректен начина€ с формулы #" << cnt + 1 << "\n";
    exit(0);
}

void fail(string s) {
    cout << "¬ывод некорректен начина€ с формулы #" << cnt + 1 << ": " << s << "\n";
    exit(0);
}

expression* last;
string last_s;
vector<string> lines;
vector<string> output;

int print_line(string expr) {
    output.puba(expr);
    //parse(expr);
    //lines.puba(expr);
    //mark_proved(parse(expr), cnt);
    //++cnt;
    return 0;
}

int act1(string expr) {
    //output.puba("act1");
    expr = "(" + expr + ")";
    print_line(expr);
    print_line(expr + " -> ((" + last_s + ") -> " + expr + ")");
    print_line("(" + last_s + ") -> " + expr);
    return 0;
}

int act2(string expr) {
    //output.puba("act2");
    expr = "(" + expr + ")";
    print_line(expr + " -> (" + expr + " -> " + expr + ")");
    print_line("(" + expr + " -> (" + expr + " -> " + expr + ")) -> (" + expr + " -> ((" + expr + " -> " + expr + ") -> " + expr + ")) -> (" + expr + " -> " + expr + ")");
    print_line("(" + expr + " -> ((" + expr + " -> " + expr + ") -> " + expr + ")) -> (" + expr + " -> " + expr + ")");
    print_line("(" + expr + " -> ((" + expr + " -> " + expr + ") -> " + expr + "))");
    print_line(expr + " -> " + expr);
    return 0;
}

int act3(string expr, pii p) {
    //output.puba("act3");
    expr = "(" + expr + ")";
    print_line("((" + last_s + ") -> (" + lines[p.ff] + ")) -> ((" + last_s + ") -> ((" + lines[p.ff] + ") -> " + expr + ")) -> ((" + last_s + ") -> " + expr + ")");
    print_line("((" + last_s + ") -> ((" + lines[p.ff] + ") -> " + expr + ")) -> ((" + last_s + ") -> " + expr + ")");
    print_line("(" + last_s + ") -> " + expr);
    return 0;
}

vector<string> lemmas;

void print_lemma(int num, string a, string b, string c) {
    string res = "";
    for (char ch : lemmas[num]) {
        if (ch == 'a') {
            res += a;
        } else if (ch == 'b') {
            res += b;
        } else if (ch == 'c') {
            res += c;
        } else {
            res += ch;
        }
    }
    res.pop_back();
    output.puba(res);
}

int main() {
    //freopen("incorrect11.in", "r", stdin);
    for (int i = 0; i < 3; ++i) {
        ifstream inf;
        string name = "lemma";
        name += (char) i + '1';
        inf.open(name);
        lemmas.puba("");
        string s;
        while (getline(inf, s)) {
            lemmas.back() += s;
            lemmas.back() += "\n";
        }
        inf.close();
    }
    getline(cin, buf);
    
    int pos = 0;
    while (buf[pos] != '|' || buf[pos + 1] != '-') {
        ++pos;
    }
    
    string res = buf.substr(pos + 2);
    string title = "";
    buf = buf.substr(0, pos);
    {
        int c = 0;
        int bal = 0;
        int from = 0;
        for (int i = 0; i < szof(buf); ++i) {
            if (buf[i] == '(') {
                ++bal;
            } else if (buf[i] == ')') {
                --bal;
            } else if (buf[i] == ',' && bal == 0) {
                string tmp = buf.substr(from, i - from);
                from = i + 1;
                title += tmp + ",";
                assump[parse(tmp)->h] = c++;
            }
        }
        last_s = buf.substr(from);
        last = parse(last_s);
    }

    if (szof(title)) {
        assert(title.back() == ',');
        title.pop_back();
    }
    title += "|- " + last_s + " -> " + res;

    output.puba(title);
    //parse(res)->print();

    while (getline(cin, buf)) {
        lines.puba(buf);
        auto cur = parse(buf);
        //cerr << cnt << endl;
        //cerr << cur->get_s() << endl;
        if (assump.count(cur->h)) {
            act1(buf);
        } else {
            bool flag = false;
            for (int i = 0; i < szof(axioms); ++i) {
                if (is_scheme(cur, axioms[i])) {
                    act1(buf);
                    flag = true;
                    break;
                }
            }
            if (!flag && last->h == cur->h) {
                act2(buf);
                flag = true;
            }
            if (!flag) {
                if (modus_ponens.count(cur->h)) {
                    auto tmp = modus_ponens[cur -> h];
                    act3(buf, tmp);
                    flag = true;
                }
            }
            if (!flag) {
                flag_tied = false;
                if (cur->name == "->") {
                    if (cur->left->name == "@") {
                        bool tmp = is_substitution(cur->right, cur->left->right, cur->left->left->name);
                        if (tmp && flag_tied) {
                            fail("терм " + term + " не свободен дл€ подстановки в формулу " + buf + " вместо переменной " + cur->left->left->name);
                        }
                        if (tmp) {
                            act1(buf);
                            flag = true;
                        }
                    }
                    if (!flag && cur->right->name == "?") {
                        bool tmp = is_substitution(cur->left, cur->right->right, cur->right->left->name);
                        if (tmp && flag_tied) {
                            fail("терм " + term + " не свободен дл€ подстановки в формулу " + buf + " вместо переменной " + cur->right->left->name);
                        }
                        if (tmp) {
                            act1(buf);
                            flag = true;
                        }
                    }
                }
            }
            if (!flag) {
                if (cur->name == "->") {
                    if (cur->right->name == "@") {
                        expression* tmp = new implication(cur->left, cur->right->right);
                        if (proved.count(tmp->h)) {
                            if (cur->left->free_vars.count(cur->right->left->h)) {
                                fail("используетс€ правило с квантором по переменной " + cur->right->left->name + ", вход€щей свободно в допущение " + cur->left->get_s());
                            }
                            if (last->free_vars.count(cur->right->left->h)) {
                                fail("переменна€ " + cur->right->left->name + " входит свободно в формулу " + last_s);
                            }
                            string a = "(" + last_s + ")", b = cur->left->get_s(), c = cur->right->right->get_s();
                            //output.puba("here1");
                            print_lemma(0, a, b, c);
                            //output.puba("(" + a + " & " + b + ") -> " + c);
                            c = cur->right->get_s();
                            output.puba("(" + a + " & " + b + ") -> " + c);
                            
                            print_lemma(1, a, b, c);
                            flag = true;
                        }
                    }
                    if (cur->left->name == "?") {
                        expression* tmp = new implication(cur->left->right, cur->right);
                        if (proved.count(tmp->h)) {
                            if (cur->right->free_vars.count(cur->left->left->h)) {
                                fail("используетс€ правило с квантором по переменной " + cur->right->left->name + ", вход€щей свободно в допущение " + cur->left->get_s());
                            }
                            if (last->free_vars.count(cur->right->left->h)) {
                                fail("переменна€ " + cur->right->left->name + " входит свободно в формулу " + last->get_s());
                            }
                            string a = "(" + last_s + ")", b = cur->left->right->get_s(), c = cur->right->get_s();
                            //output.puba("here2");
                            print_lemma(2, a, b, c);
                            //output.puba(b + " -> (" + a + " -> " + c + ")");
                            b = cur->left->get_s();
                            output.puba(b + " -> (" + a + " -> " + c + ")");

                            print_lemma(2, b, a, c);
                            flag = true;
                        }
                    }
                    if (cur->left->name == "&" && cur->left->right->name == "@" && cur->left->right->right->name == "->") {
                        expression *a = cur->left->left, *b = cur->left->right->right->left, *c = cur->left->right->right->right, *d = cur->right;
                        string var = cur->left->right->left->name;
                        if (b->h == d->h && b->free_vars.count(get_hash(var))) {
                            bool tmp = is_substitution(a, b, var);
                            if (tmp && scheme::have[get_hash(var)] == get_hash("0")) {
                                bool tmp2 = is_substitution(c, b, var);
                                if (tmp2 && scheme::have[get_hash(var)] == increment(new variable(var)).h) {
                                    act1(buf);
                                    flag = true;
                                }
                            }
                        }
                    }
                }
            }
            if (!flag) {
                cerr << buf << endl;
                fail();
            }
        }
        mark_proved(cur, cnt);
        ++cnt;
    }

    for (auto s : output) {
        cout << s << "\n";
    }
    
    #ifdef LOCAL
        cerr << "time: " << clock() << endl;
    #endif
    return 0;
}