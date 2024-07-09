# include <bits/stdc++.h>
using namespace std;
#pragma GCC optimize("Ofast")
#pragma GCC optimize("unroll-loops")

using ll = long long;
using u32 = unsigned int;
using u64 = unsigned long long;
using i128 = __int128;

template <class T>
constexpr T infty = 0;
template <>
constexpr int infty<int> = 1'000'000'000;
template <>
constexpr ll infty<ll> = ll(infty<int>) * infty<int> * 2;
template <>
constexpr u32 infty<u32> = infty<int>;
template <>
constexpr u64 infty<u64> = infty<ll>;
template <>
constexpr i128 infty<i128> = i128(infty<ll>) * infty<ll>;
template <>
constexpr double infty<double> = infty<ll>;
template <>
constexpr long double infty<long double> = infty<ll>;

using pi = pair<int, int>;
using vi = vector<int>;
using pll = pair<ll, ll>;
using vll = vector<ll>;
template <class T>
using vc = vector<T>;
template <class T>
using pq = priority_queue<T>;
template <class T>
using pqg = priority_queue<T, vector<T>, greater<T>>;

# define rep1(a) for (int _ = 0; _ < (a); ++_)
# define rep2(i, a) for (int i = 0; i < (a); ++i)
# define rep3(i, a, b) for (int i = a; i < (b); ++i)
# define rep4(i, a, b, c) for (int i = a; i < (b); i += (c))
# define per1(a) for (int _ = (a) - 1; _ >= (0); --_)
# define per2(i, a) for (int i = (a) - 1; i >= (0); --i)
# define per3(i, a, b) for (int i = (b) - 1; i >= (a); --i)
# define per4(i, a, b, c) for (int i = (b) - 1; i >= (a); i -= (c))
# define overload4(a, b, c, d, e, ...) e
# define rep(...) overload4(__VA_ARGS__, rep4, rep3, rep2, rep1)(__VA_ARGS__)
# define per(...) overload4(__VA_ARGS__, per4, per3, per2, per1)(__VA_ARGS__) 
# define for_subset(t, s) for (int t = (s); t >= 0; t = (t == 0 ? -1 : (t - 1) & (s)))

# define all(x) x.begin(), x.end()
# define len(x) int(x.size())
# define elif else if
# define eb emplace_back
# define mp make_pair
# define mt make_tuple
# define fi first
# define se second
# define stoi stoll

int popcnt(int x) {return __builtin_popcount(x);}
int popcnt(u32 x) {return __builtin_popcount(x);}
int popcnt(ll x) {return __builtin_popcountll(x);}
int popcnt(u64 x) {return __builtin_popcountll(x);}
int topbit(int x) {return (x == 0 ? -1 : 31 - __builtin_clz(x));}
int topbit(u32 x) {return (x == 0 ? -1 : 31 - __builtin_clz(x));}
int topbit(ll x) {return (x == 0 ? -1 : 63 - __builtin_clzll(x));}
int topbit(u64 x) {return (x == 0 ? -1 : 63 - __builtin_clzll(x));}
int lowbit(int x) {return (x == 0 ? -1 : __builtin_ctz(x));}
int lowbit(u32 x) {return (x == 0 ? -1 : __builtin_ctz(x));}
int lowbit(ll x) {return (x == 0 ? -1 : __builtin_ctzll(x));}
int lowbit(u64 x) {return (x == 0 ? -1 : __builtin_ctzll(x));}

template <typename T, typename U>
T ceil(T x, U y) {
	return (x > 0 ? (x + y - 1) / y : x / y);
}
template <typename T, typename U>
T floor(T x, U y) {
	return (x > 0 ? x / y : (x - y + 1) / y);
}
template <typename T, typename U>
pair<T, T> divmod(T x, U y) {
	T q = floor(x, y);
	return {q, x - q * y};
}

template <typename T, typename U>
T SUM(const vector<U>& A) {
	T sum = 0;
	for (auto&& a: A) sum += a;
	return sum;
}
#define MIN(v) *min_element(all(v))
#define MAX(v) *max_element(all(v))
#define LB(c, x) distance((c).begin(), lower_bound(all(c), (x)))
#define UB(c, x) distance((c).begin(), upper_bound(all(c), (x)))
#define UNIQUE(x) sort(all(x)), x.erase(unique(all(x)), x.end()), x.shrink_to_fit()

template <typename F>
ll binary_search(F check, ll ok, ll ng, bool check_ok = true) {
	if (check_ok) assert(check(ok));
	while (abs(ok - ng) > 1) {
		auto x = (ng + ok) / 2;
		tie(ok, ng) = (check(x) ? mp(x, ng) : mp(ok, x));
	}
	return ok;
}
template <typename F>
double binary_search_real(F check, double ok, double ng, int iter = 100) {
	rep(iter) {
		double x = (ok + ng) / 2;
		tie(ok, ng) = (check(x) ? mp(x, ng) : mp(ok, x));
	}
	return (ok + ng) / 2;
}

template <class T, class S>
inline bool chmax(T& a, const S& b) {
	return (a < b ? a = b, 1 : 0);
}
template <class T, class S>
inline bool chmin(T& a, const S& b) {
	return (a > b ? a = b, 1 : 0);
}

vc<int> s_to_vi(const string& S, char first_char) {
	vc<int> A(S.size());
	rep(i, S.size()) {A[i] = (S[i] != '?' ? S[i] - first_char : -1);}
	return A;
}

template <typename T, typename U>
vector<T> cumsum(vector<U>& A, int off = 1) {
	int N = A.size();
	vector<T> B(N + 1);
	rep(i, N) B[i + 1] = B[i] + A[i];
	if (off == 0) B.erase(B.begin());
	return B;
}

//stable sort
template <typename T>
vector<int> argsort(const vector<T>& A) {
	vector<int> ids(len(A));
	iota(all(ids), 0);
	sort(all(ids), [&](int i, int j){
		return (A[i] == A[j] ? i < j : A[i] < A[j]);
	});
	return ids;
}

// A[I[0]], A[I[1]], ...
template <typename T>
vc<T> rearrange(const vc<T>& A, const vc<int>& I) {
	vc<T> B(len(I));
	rep(i, len(I)) B[i] = A[I[i]];
	return B;
}

template <typename T, typename U>
ostream& operator<<(ostream& os, const pair<T, U>& A) {
  os << A.fi << " " << A.se;
  return os;
}

template <typename T>
ostream& operator<<(ostream& os, const vector<T>& A) {
  for (size_t i = 0; i < A.size(); i++) {
    if(i) os << " ";
    os << A[i];
  }
  return os;
}

void bug() {
  cerr << "\n";
  cerr.flush();
}

template <class Head, class... Tail>
void bug(Head&& head, Tail&&... tail) {
  cerr << head;
  if (sizeof...(Tail)) cerr << " ";
  bug(forward<Tail>(tail)...);
}

void YES(bool t = 1) {cout << (t ? "YES" : "NO") << endl;}
void NO(bool t = 1) {YES(!t);}
void Yes(bool t = 1) {cout << (t ? "Yes" : "No") << endl;}
void No(bool t = 1) {Yes(!t);}
void yes(bool t = 1) {cout << (t ? "yes" : "no") << endl;}
void no(bool t = 1) {yes(!t);}
//-------------------- template ending --------------------

// checked
struct dsu {
public:
	dsu() : _n(0) {}
	explicit dsu(int n) : _n(n), parent_or_size(n, -1) {}
	int merge(int a, int b) {
		assert(0 <= a && a < _n);
		assert(0 <= b && b < _n);
		int x = leader(a), y = leader(b);
		if (x == y) return x;
		if (-parent_or_size[x] < -parent_or_size[y]) swap(x, y);
		parent_or_size[x] += parent_or_size[y];
		parent_or_size[y] = x;
		return x;
	}
	bool same(int a, int b) {
		assert(0 <= a && a < _n);
		assert(0 <= b && b < _n);
		return leader(a) == leader(b);
	}
	int leader(int a) {
		assert(0 <= a && a < _n);
		if (parent_or_size[a] < 0) return a;
		return parent_or_size[a] = leader(parent_or_size[a]);
	}
	int size(int a) {
		assert(0 <= a && a < _n);
		return -parent_or_size[leader(a)];
	}
	vector<vi> groups() {
		vi leader_buf(_n), group_size(_n);
		rep(i, 0, _n) {
			leader_buf[i] = leader(i);
			group_size[leader_buf[i]]++;
		}
		vector<vi> result(_n);
		rep(i, 0, _n) result[i].reserve(group_size[i]);
		rep(i, 0, _n) result[leader_buf[i]].eb(i);
		result.erase(remove_if(all(result), [&](vi& v){return v.empty();}), result.end());
		return result;
	}
private:
	int _n;
	vi parent_or_size;
};

struct Service {
	int s, t, l, r, v;
	vi path;
};

constexpr int K = 40;

int main()
{
    ios::sync_with_stdio(false); cin.tie(0);
	int n, m;
	cin >> n >> m;
	assert(n >= 2 and n <= 200);
	assert(m >= 1 and m <= 1000);
	vc<pi> edge;
	vi power;
	edge.resize(m);
	power.resize(n);
	rep(i, n) {
		cin >> power[i];
		assert(power[i] >= 0 and power[i] <= 20);
	} 
	dsu ds(n);
	vc<vi> g(n);
	rep(i, m) {
		cin >> edge[i].fi >> edge[i].se;
		assert(edge[i].fi >= 1 and edge[i].fi <= n);
		assert(edge[i].se >= 1 and edge[i].se <= n);
		assert(edge[i].fi != edge[i].se);
		edge[i].fi--; edge[i].se--;
		ds.merge(edge[i].fi, edge[i].se);
		g[edge[i].fi].eb(i);
		g[edge[i].se].eb(i);
	}
	assert(ds.size(0) == n);
	vector<bitset<K>> status(m, (1ll << K) - 1);
	int J;
	cin >> J;
	vector<Service> services;
	assert(J >= 1 and J <= 5000);
	rep(J) {
		Service s;
		int pn;
		cin >> s.s >> s.t >> pn >> s.l >> s.r >> s.v;
		assert(1 <= s.s and s.s <= n);
		assert(1 <= s.t and s.t <= n);
		assert(1 <= s.l and s.l <= 40);
		assert(1 <= s.r and s.r <= 40);
		assert(s.l <= s.r);
		assert(0 <= s.v and s.v <= 100000);
		s.s--;
		s.t--;
		s.l--;
		s.r--;
		rep(i, pn) {
			int x;
			cin >> x;
			assert(1 <= x and x <= m);
			x--;
			s.path.eb(x);
		}
		int start = s.s;
		ll ck = (1ll << (s.r + 1)) - 1;
		ck ^= (1ll << s.l) - 1;
		bitset<K> bt(ck);
		set<int> nodes, edges;
		for (auto e : s.path) {
			assert(edges.count(e) == 0);
			assert(nodes.count(start) == 0);
			edges.insert(e);
			nodes.insert(start);
			assert(start == edge[e].fi or start == edge[e].se);
			assert((bt & status[e]) == bt);
			status[e] ^= ck;
			start = (edge[e].fi == start ? edge[e].se : edge[e].fi);
		}
		assert(s.t == start);
	}
	
	cout << 0 << endl;
	
	int T;
	cin >> T;
	assert(1 <= T and T <= 100);
	int cnt = 0;
	while (T--) {
		int fail;
		set<int> fail_set;
		while (true) {
			cin >> fail;
			if (fail == -1) break;
			cnt++;
			assert(fail >= 1 and fail <= m);
			assert(fail_set.count(fail) == 0);
			fail_set.insert(fail);
			cout << 0 << endl;
		}
		assert(fail_set.size() <= 50);
	}
    return 0;
}
