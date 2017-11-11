#include "bits/stdc++.h"
#define puba push_back
#define ff first
#define ss second
#define bend(_x) begin(_x), end(_x)
#define szof(_x) ((int) (_x).size())
#define TASK_NAME ""

using namespace std;
typedef long long ll;
typedef pair<int, int> pii;
const int INF = 1e9 + 7;
const ll INFL = 1e18 + 123;
const double PI = atan2(0, -1);
mt19937 tw(960172);
ll rnd(ll x, ll y) { static uniform_int_distribution<ll> d; return d(tw) % (y - x + 1) + x; }

vector<string> init, proof1, lemma, proof2, morgan;

void read(string name, vector<string>& v) {
    ifstream inp(name);
    string s;
    while (getline(inp, s)) {
        v.puba(s);
    }
}

int main() {
    //freopen(TASK_NAME ".in", "r", stdin);
    //freopen(TASK_NAME ".out", "w", stdout);
    cerr << fixed << setprecision(15);
    cout << fixed << setprecision(15);
    
    int a, b;
    scanf("%d%d", &a, &b);
    string vala = "0" + string(a, '\'');
    string valb = "0" + string(b, '\'');
        

    read("init", init);
    read("proof1", proof1);
    read("lemma", lemma);
    read("proof2", proof2);
    read("morgan", morgan);

    int c = b - a;
    if (c >= 0) {
        string valc = "0" + string(c, '\'');
        cout << "|-" << "?p(" << vala << " + p) = " << valb << "\n"; 
        
        for (string s : init) {
            cout << s << "\n";
        }
        
        cout << "@a(a + 0 = a) -> " << vala << " + 0 = " << vala << "\n";
        cout << vala << " + 0 = " << vala << "\n";
        string res = "";
        for (string s : proof1) {
            for (char ch : s) {
                if (ch == 'A') {
                    res += vala;
                } else {
                    res += ch;
                }
            }
            res += "\n";
        }
        string pl = "";
        for (int i = 0; i < c; ++i) {
            for (char ch : res) {
                if (ch == '#') {
                    cout << pl;
                } else {
                    cout << ch;
                }
            }
            pl += '\'';
        }
        cout << "(" << vala << " + " << valc << ") = " << valb << " -> ?p(" << vala << " + p) = " << valb << "\n";
        cout << "?p(" << vala << " + p) = " << valb << "\n";
    } else {
        cout << "|-" << "!(?p(" << vala << " + p) = " << valb << ")\n"; 
        for (string s : init) {
            cout << s << "\n";
        }
        for (string s : lemma) {
            cout << s << "\n";
        }
        c = -c;
        string C0 = string(c - 1, '\''), B = string(b, '\'');
        for (string s : proof2) {
            for (char ch : s) {
                if (ch == 'C') {
                    cout << C0;
                } else if (ch == 'B'){
                    cout << B;
                } else {
                    cout << ch;
                }
            }
            cout << "\n";
        }
        for (string s : morgan) {
            for (char ch : s) {
                if (ch == 'C') {
                    cout << C0;
                } else if (ch == 'B'){
                    cout << B;
                } else {
                    cout << ch;
                }
            }
            cout << "\n";
        }
    }
    
    
    
    #ifdef LOCAL
        cerr << "time: " << clock() << endl;
    #endif
    return 0;
}