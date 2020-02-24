/***********************************************************************
Copyright (c) 2014-2019, Jan Elffers
Copyright (c)      2019, Jo Devriendt

Parts of the code were copied or adapted from Minisat.

MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
           Copyright (c) 2007-2010  Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
***********************************************************************/

//TODO: generate cuts after each found solution
//TODO: don't use objective function during search

using namespace std;
#include <vector>
#include <iostream>
#include <sstream>
#include <fstream>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <cassert>
#include <cstring>
#include <csignal>
#include <map>
#include <set>
#include <limits>

#define _unused(x) ((void)(x)) // marks variables unused in release mode

void exit_SAT(),exit_UNSAT(),exit_INDETERMINATE(),exit_OPT(),exit_ERROR(const std::initializer_list<std::string>&);

// Minisat cpuTime function
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>

#include "aux.h"

static inline double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }

struct Clause {
	struct {
		unsigned markedfordel : 1;
		unsigned learnt       : 1;
		unsigned size         : 30; } header;
	// watch data
	int nwatch;
	long long sumwatchcoefs;
	long long minsumwatch;
	// ordinary data
	int w;
	float act;
	int lbd;
	int data[0];

	size_t size() const { return header.size; }
	
	int * lits() { return data; }
	int * coefs() { return (int*)(data+header.size); }
	
	bool learnt() const { return header.learnt; }
	bool markedfordel() const { return header.markedfordel; }
	void markfordel() { header.markedfordel=1; }
};
struct lit{int l;lit(int l):l(l){}};
ostream&operator<<(ostream&o,lit const&l){if(l.l<0)o<<"~";o<<"x"<<abs(l.l);return o;}
ostream & operator<<(ostream & o, Clause & C) {
	vector<int> order;
	for (int i = 0; i < (int) C.size(); i++) order.push_back(i);
	sort(order.begin(), order.end(), [&C](int i, int j) { return abs(C.lits()[i]) < abs(C.lits()[j]); });
	for (int i = 0; i < (int) C.size(); i++) {
		int l = C.lits()[order[i]];
		int coef = C.coefs()[order[i]];
		o << coef << " " << lit(l) << " ";
	}
	o << ">= " << C.w << ";";
	return o;
}

// ---------------------------------------------------------------------
// memory. maximum supported size of learnt clause database is 16GB
struct CRef {
	uint32_t ofs;
	bool operator==(CRef const&o)const{return ofs==o.ofs;}
	bool operator!=(CRef const&o)const{return ofs!=o.ofs;}
	bool operator< (CRef const&o)const{return ofs< o.ofs;}
};

const CRef CRef_Undef = { UINT32_MAX };
const CRef CRef_Unsat = { UINT32_MAX-1 }; // TODO: ask Jan if this limit will ever be reached

class OutOfMemoryException{};
static inline void* xrealloc(void *ptr, size_t size)
{
	void* mem = realloc(ptr, size);
	if (mem == NULL && errno == ENOMEM){
		throw OutOfMemoryException();
	}else
		return mem;
}
struct {
	uint32_t* memory;
	uint32_t at, cap;
	uint32_t wasted; // for GC
	void capacity(uint32_t min_cap)
	{
		if (cap >= min_cap) return;

		uint32_t prev_cap = cap;
		while (cap < min_cap){
			// NOTE: Multiply by a factor (13/8) without causing overflow, then add 2 and make the
			// result even by clearing the least significant bit. The resulting sequence of capacities
			// is carefully chosen to hit a maximum capacity that is close to the '2^32-1' limit when
			// using 'uint32_t' as indices so that as much as possible of this space can be used.
			uint32_t delta = ((cap >> 1) + (cap >> 3) + 2) & ~1;
			cap += delta;

			if (cap <= prev_cap)
				throw OutOfMemoryException();
		}
		// printf(" .. (%p) cap = %u\n", this, cap);

		assert(cap > 0);
		memory = (uint32_t*) xrealloc(memory, sizeof(uint32_t) * cap);
	}
	int sz_clause(int length) { return (sizeof(Clause)+sizeof(int)*length+sizeof(int)*length)/sizeof(uint32_t); }
	CRef alloc(vector<int> lits, vector<int> coefs, int w, bool learnt){
		assert(!lits.empty());
		int length = (int) lits.size();
		// note: coefficients can be arbitrarily ordered (we don't sort them in descending order for example)
		// during maintenance of watches the order will be shuffled.
		capacity(at + sz_clause(length));
		Clause * clause = (Clause*)(memory+at);
		new (clause) Clause;
		at += sz_clause(length);
		clause->header = {0, learnt, (unsigned)length};
		clause->w = w;
		clause->act = 0;
		for(int i=0;i<length;i++)clause->lits()[i]=lits[i];
		for(int i=0;i<length;i++)clause->coefs()[i]=coefs[i];
		return {(uint32_t)(at-sz_clause(length))};
	}
	Clause& operator[](CRef cr) { return (Clause&)*(memory+cr.ofs); }
	const Clause& operator[](CRef cr) const { return (Clause&)*(memory+cr.ofs); }
} ca;
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
int verbosity = 1;
// currently, the maximum number of variables is hardcoded (variable N), and most arrays are of fixed size.
int n = 0;
bool opt = false;
int opt_K = 0;
int opt_normalize_add = 0, opt_coef_sum = 0;
int nbWcnfAuxVars = 0;
inline int getNbOrigVars(){ return n-opt_K-nbWcnfAuxVars; }
vector<CRef> clauses, learnts;
struct Watch {
	CRef cref;
};

template <class T>
inline T ceildiv(const T& p,const T& q){ assert(q>0); assert(p>=0); return (p+q-1)/q; }
template <class T>
inline T floordiv(const T& p,const T& q){ assert(q>0); assert(p>=0); return p/q; }
template <class T>
inline T ceildiv_safe(const T& p,const T& q){ assert(q>0); return (p<0?-floordiv(-p,q):ceildiv(p,q)); }
template <class T>
inline T floordiv_safe(const T& p,const T& q){ assert(q>0); return (p<0?-ceildiv(-p,q):floordiv(p,q)); }
template <class T>
inline T mod_safe(const T& p,const T& q){ assert(q>0); return p<0?q-(-p%q):p%q; }
template <class T>
inline T mir_coeff(const T& ai,const T& b, const T& d){
	assert(d>0);
	T bmodd=mod_safe(b,d);
	return bmodd*floordiv_safe(ai,d)+min(mod_safe(ai,d),bmodd);
}

vector<vector<Watch>> _adj; vector<vector<Watch>>::iterator adj;
vector<CRef> _Reason; vector<CRef>::iterator Reason;
vector<int> trail;
vector<int> _Level; vector<int>::iterator Level;
vector<int> trail_lim;
int qhead; // for unit propagation
vector<int> phase;
vector<int> lpPhase;
void newDecisionLevel() { trail_lim.push_back(trail.size()); }
int decisionLevel() { return trail_lim.size(); }

template<class SMALL, class LARGE> // LARGE should be able to fit sums of SMALL
struct Constraint{
	std::vector<int> vars;
	vector<SMALL> coefs;
	LARGE rhs = 0;

	void reset(){
		for(int v: vars) coefs[v]=std::numeric_limits<SMALL>::min();
		vars.clear();
		rhs=0;
	}

	void init(std::vector<int>& lits, std::vector<SMALL>& cs, LARGE& w){
		reset();
		for(int i=0; i<lits.size(); ++i) addLhs(cs[i],lits[i]);
		addRhs(w);
	}

	void addLhs(SMALL c, int l){ // treat negative literals as 1-v
		if(c==0) return;
		int v = l;
		if(l<0){
			rhs -= c;
			c = -c;
			v = -l;
		}
		if((int)coefs.size()<=v) coefs.resize(v+1,std::numeric_limits<SMALL>::min());
		if(coefs[v]==std::numeric_limits<SMALL>::min()) vars.push_back(v), coefs[v]=0;
		coefs[v]+=c;
	}

	inline void addRhs(SMALL r){ rhs+=r; }
	inline LARGE getRhs(){ return rhs; }
	inline LARGE getDegree() {
		LARGE result = rhs;
		for (int v: vars) result -= min(0,coefs[v]); // considering negative coefficients
		return result;
	}

	void saturate(){
		LARGE w = getDegree();
		if(w<=0) reset(), rhs=w;
		for (int v: vars){
			if(coefs[v]>w) coefs[v]=w;
			if(coefs[v]<-w) rhs-=coefs[v]+w, coefs[v]=-w;
		}
		assert(w==getDegree()); // degree is invariant under saturation
	}

	void divide(SMALL d){
		for (int v: vars) coefs[v] = ceildiv_safe<SMALL>(coefs[v],d);
		rhs=ceildiv_safe<LARGE>(rhs,d);
	}

	void getNormalForm(std::vector<int>& lits, std::vector<SMALL>& cs, LARGE& w){
		lits.clear(); cs.clear();
		w=getDegree();
		if(w<=0) return;
		lits.reserve(vars.size()); cs.reserve(vars.size());
		for(int v: vars){
			if(coefs[v]<0){
				lits.push_back(-v);
				cs.push_back(min<LARGE>(-coefs[v],w));
			}else if(coefs[v]>0){
				lits.push_back(v);
				cs.push_back(min<LARGE>(coefs[v],w));
			}
		}
	}

	bool isUsed(int l){ return coefs.size()>abs(l) && coefs[abs(l)]!=std::numeric_limits<SMALL>::min(); }

	void print(){
		sort(vars.begin(),vars.end(),[&](SMALL v1,SMALL v2){return v1<v2;});
		for(int v: vars) std::cout << coefs[v] << "x" << v << " ";
		std::cout << ">= " << rhs << " (" << getDegree() << ")" << std::endl;
	}

	void printNormalForm(){
		sort(vars.begin(),vars.end(),[&](SMALL v1,SMALL v2){return v1<v2;});
		std::vector<int> lits; std::vector<SMALL> cs; LARGE w;
		getNormalForm(lits,cs,w);
		for(int i=0; i<(int)lits.size(); ++i){
			int l = lits[i];
			std::cout << cs[i] << "x" << l << ":" << (Level[l]>0?"1":(Level[-l]>0?"0":"")) << "." << max(Level[l],Level[-l]) << " ";
		}
		std::cout << ">= " << w << std::endl;
	}

	void invert(){
		for(int v: vars) coefs[v]=-coefs[v];
		rhs=-rhs;
	}
};
Constraint<int, long long> tmpConstraint;

double initial_time;
int NCONFL=0, NDECIDE=0, NGENEREALPB=0;
long long NPROP=0, NIMPL=0;
double LPSOLVETIME=0, LPTIME=0, LPCUTTIME;
int NLPCALLS=0, NLPFARKAS=0, NLPCONSTR=0, NLPPIVOTS=0, NLPNOFARKAS=0, NLPNOPRIMAL=0, NLPGOMORYCUTS=0, NLPNOPIVOT=0;
int NLPGOMORYCUTSINTERNAL=0, NLPGOMORYCUTSINTERNALINFEASIBLE=0;
int NLPINFEAS=0, NLPOPTIMAL=0, NLPCYCLING=0, NLPSINGULAR=0, NLPOTHER=0, NLPRESETBASIS=0;
long long NLPPHASEDIFF=0, NLPLEARNEDCUTS=0, NLPDUALCUTS=0, NLPDELETEDCUTS=0;
double AVGCONFLDEPTH=0, AVGLPINFEASDEPTH=0;
double rinc = 2;
int rfirst = 100;
int nbclausesbeforereduce=2000;
int incReduceDB=300;
double lpmulti = 0.0;
bool useLpPhase = false;
double sanitizeFarkas = 1e-6;
bool learnCuts = false;
bool addDualCuts = false;
bool addGomoryCuts = false;
bool deleteCuts = false;
double tolerance = 1e-6;
double maxCutCos = 0.9;
int cutRoundLimit = 300;
bool useInternalOptimality = false;
int lpObjectiveCoef = 1;

// VSIDS ---------------------------------------------------------------
double var_decay=0.95;
double var_inc=1.0;
vector<double> activity;
struct{
	// segment tree (fast implementation of priority queue).
	vector<int> tree;
	void init() {
		tree.clear();
		tree.resize(2*(n+1), -1);
	}
	void percolateUp(int x) {
		for(int at=x+n+1; at>1; at>>=1){
			if(tree[at^1]==-1 || activity[x]>activity[tree[at^1]])tree[at>>1]=x;else break;
		}
	}
	bool empty() { return tree[1] == -1; }
	void insert(int x) {
		tree[x+n+1] = x;
		percolateUp(x);
	}
	int removeMax() {
		int x = tree[1];
		assert(x != -1);
		tree[x+n+1] = -1;
		for(int at=x+n+1; at>1; at>>=1){
			if(tree[at^1] != -1 && (tree[at]==-1 || activity[tree[at^1]]>activity[tree[at]]))tree[at>>1]=tree[at^1];else tree[at>>1]=tree[at];
		}
		return x;
	}
	bool inHeap(int v) { return tree[v+n+1] != -1; }
} order_heap;
void insertVarOrder(int x) {
	if (!order_heap.inHeap(x)) order_heap.insert(x); }

void varDecayActivity() { var_inc *= (1 / var_decay); }
void varBumpActivity(int v){
	if ( (activity[v] += var_inc) > 1e100 ) {
		// Rescale:
		for (int i = 1; i <= n; i++)
			activity[i] *= 1e-100;
		var_inc *= 1e-100; }

	// Update order_heap with respect to new activity:
	if (order_heap.inHeap(v))
		order_heap.percolateUp(v); }
// CLAUSE VSIDS --------------------------------------------------------
double cla_inc=1.0;
double clause_decay=0.999;
void claDecayActivity() { cla_inc *= (1 / clause_decay); }
void claBumpActivity (Clause& c) {
		if ( (c.act += cla_inc) > 1e20 ) {
			// Rescale:
			for (size_t i = 0; i < learnts.size(); i++)
				ca[learnts[i]].act *= 1e-20;
			cla_inc *= 1e-20; } }
// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

template<class A,class B> long long slack(int length,A const& lits,B const& coefs,long long w){
	long long s=-w;
	for(int i=0;i<length;i++){
		int l = lits[i];
		int coef = coefs[i];
		if(Level[-l]==-1)s+=coef;
	}
	return s;
}

long long slack(Clause & C){ return slack(C.size(),C.lits(),C.coefs(),C.w); }

// TODO: ask Jan what happens when a propagating or empty clause is attached
void attachClause(CRef cr){
	Clause & C = ca[cr];
	// sort literals by the decision level at which they were falsified, descending order (never falsified = level infinity)
	vector<pair<int,int>> order;
	for(int i=0;i<(int)C.size();i++){
		int lvl=Level[-C.lits()[i]]; if(lvl==-1)lvl=1e9;
		order.emplace_back(-lvl,i);
	}
	sort(order.begin(),order.end());
	vector<int>lits_old (C.lits(), C.lits()+C.size());
	vector<int>coefs_old (C.coefs(), C.coefs()+C.size());
	for(int i=0;i<(int)C.size();i++){
		C.lits()[i] = lits_old[order[i].second];
		C.coefs()[i] = coefs_old[order[i].second];
	}
	C.sumwatchcoefs = 0;
	C.nwatch = 0;
	int mxcoef = 0; for(int i=0;i<(int)C.size();i++) if (abs(C.lits()[i]) <= n - opt_K) mxcoef = max(mxcoef, C.coefs()[i]);
	C.minsumwatch = (long long) C.w + mxcoef;
	for(int i=0;i<(int)C.size();i++) {
		C.sumwatchcoefs += C.coefs()[i];
		C.nwatch++;
		adj[C.lits()[i]].push_back({cr});
		if (C.sumwatchcoefs >= C.minsumwatch) break;
	}
}

bool locked(CRef cr){
	Clause & c = ca[cr];
	for(size_t idx=0;idx<c.size();idx++){
		if(Reason[c.lits()[idx]] == cr) return true;
	}
	return false;
}

void removeClause(CRef cr){
	Clause& c = ca[cr];
	assert(!c.markedfordel());
	assert(!locked(cr));
	c.markfordel();
	ca.wasted += ca.sz_clause(c.size());
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
void uncheckedEnqueue(int p, CRef from){
	assert(Level[p]==-1 && Level[-p]==-1);
	Level[p] = -2;
	Reason[p] = from;
	trail.push_back(p);
}

void undoOne(){
	assert(!trail.empty());
	int l = trail.back();
	trail.pop_back();
	Level[l] = -1;
	phase[abs(l)]=l;
	lpPhase[abs(l)]=l;
	if(!trail_lim.empty() && trail_lim.back() == (int)trail.size())trail_lim.pop_back();
	Reason[l] = CRef_Undef;
	insertVarOrder(abs(l));
}

void backjumpTo(int level){
	while(decisionLevel()>level) undoOne();
	qhead = trail.size();
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
/**
 * In the conflict analysis we represent the learnt clause
 * by an array of length 2*N, with one position per literal.
 * 
 * After each analyze() we want to reset this array.
 * Because this is expensive we keep track of which literals participate
 * in the analysis and reset only their coefficients.
 */
struct ConflictData {
	long long slack;
	int cnt_falsified_currentlvl;
	// here we use int64 because we could get overflow in the following case:
	// the reason's coefs multiplied by the coef. of the intermediate conflict clause
	vector<long long> _M; vector<long long>::iterator M;
	long long w;
	vector<int> used; // 1: used, 2: clashing in some step
	vector<int> usedlist;
	void init(){
		_M.resize(2*n+1, 0);
		M = _M.begin() + n;
		used.resize(n+1, 0);
		usedlist.reserve(n);
		reset();
	}
	void reset(){
		slack=0;
		cnt_falsified_currentlvl=0;
		w=0;
		for(int x:usedlist)M[x]=M[-x]=0,used[x]=0;
		usedlist.clear();
	}
	void use(int x){
		if(!used[x])used[x]=max(used[x],1),usedlist.push_back(x);
	}
} confl_data;

void round_reason(int l0, vector<int>&out_lits,vector<int>&out_coefs,int&out_w) {
	Clause & C = ca[Reason[l0]];
	int old_coef_l0 = C.coefs()[find(C.lits(),C.lits()+C.size(),l0)-C.lits()];
	int w = C.w;
	for(size_t i=0;i<C.size();i++){
		int l = C.lits()[i];
		int coef = C.coefs()[i];
		if (Level[-l] == -1) {
			if (coef % old_coef_l0 != 0) w -= coef;
			else out_lits.push_back(l), out_coefs.push_back(coef / old_coef_l0);
			
			// partial weakening would instead do:
			/*w -= coef % old_coef_l0;
			if (coef >= old_coef_l0) out_lits.push_back(l), out_coefs.push_back(coef / old_coef_l0);*/
		} else {
			out_lits.push_back(l), out_coefs.push_back(ceildiv(coef, old_coef_l0));
		}
	}
	out_w = ceildiv<long long>(w, old_coef_l0);
	assert(slack(out_lits.size(), out_lits, out_coefs, out_w) == 0);
}

void round_conflict(long long c) {
	for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]){
		if (Level[-l] == -1) {
			if (confl_data.M[l] % c != 0) {
				confl_data.w -= confl_data.M[l], confl_data.M[l] = 0;
			} else confl_data.M[l] /= c;
			
			// partial weakening would instead do:
			/*confl_data.w -= confl_data.M[l] % c;
			confl_data.M[l] /= c;*/
		} else confl_data.M[l] = ceildiv(confl_data.M[l], c);
	}
	confl_data.w = ceildiv(confl_data.w, c);
	confl_data.slack = -ceildiv(-confl_data.slack, c);
}

template<class It1, class It2> void add_to_conflict(size_t size, It1 const&reason_lits,It2 const&reason_coefs,int reason_w){
	vector<long long>::iterator M = confl_data.M;
	long long & w = confl_data.w;
	w += reason_w;
	bool overflow = false;
	for(size_t it=0;it<size;it++){
		int l = reason_lits[it];
		int c = reason_coefs[it];
		assert(c>0);
		confl_data.use(abs(l));
		if (M[-l] > 0) {
			confl_data.used[abs(l)] = 2;
			if (c >= M[-l]) {
				if (Level[l] == decisionLevel()) confl_data.cnt_falsified_currentlvl--;
				M[l] = c - M[-l];
				w -= M[-l];
				M[-l] = 0;
				if (Level[-l] == decisionLevel() && M[l] > 0) confl_data.cnt_falsified_currentlvl++;
			} else {
				M[-l] -= c;
				w -= c;
			}
		} else {
			if (Level[-l] == decisionLevel() && M[l] == 0) confl_data.cnt_falsified_currentlvl++;
			M[l] += c;
		}
		if (M[l] > (int) 1e9) overflow = true;
	}
	if (w > (int) 1e9 || overflow) {
		// round to cardinality.
		long long d = 0;
		for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)d=max(d, confl_data.M[l]);
		round_conflict(d);
	}
}

//TODO: what is LBD of clauses with unknown literals? +1 for each unknown literal?
int computeLBD(CRef cr) {
	Clause & C = ca[cr];
	set<int> levels;
	int * lits = C.lits();
	for (int i=0; i<(int)C.size(); i++) if (Level[-lits[i]] != -1) levels.insert(Level[-lits[i]]);
	return (int) levels.size();
}

void analyze(CRef confl, vector<int>& out_lits, vector<int>& out_coefs, int& out_w){
	Clause & C = ca[confl];
	if (C.learnt()) {
		claBumpActivity(C);
		if (C.lbd > 2) C.lbd = min(C.lbd, computeLBD(confl));
	}
	add_to_conflict(C.size(), C.lits(), C.coefs(), C.w);
	confl_data.slack = slack(C);
	vector<int> reason_lits; reason_lits.reserve(n);
	vector<int> reason_coefs; reason_coefs.reserve(n);
	int reason_w;
	while(1){
		if (decisionLevel() == 0) {
			exit_UNSAT();
		}
		int l = trail.back();
		if(confl_data.M[-l]) {
			confl_data.M[-l] = min(confl_data.M[-l], confl_data.w); // so that we don't round the conflict if w=1.
			if (confl_data.M[-l] > 1) {
				round_conflict(confl_data.M[-l]);
			}
			if (confl_data.cnt_falsified_currentlvl == 1) {
				break;
			} else {
				assert(Reason[l] != CRef_Undef);
				if (ca[Reason[l]].learnt()) {
					claBumpActivity(ca[Reason[l]]);
					if (ca[Reason[l]].lbd > 2) ca[Reason[l]].lbd = min(ca[Reason[l]].lbd, computeLBD(Reason[l]));
				}
				reason_lits.clear();
				reason_coefs.clear();
				round_reason(l, reason_lits, reason_coefs, reason_w);
				add_to_conflict(reason_lits.size(), reason_lits, reason_coefs, reason_w);
			}
		}
		int oldlvl=decisionLevel();
		undoOne();
		if(decisionLevel()<oldlvl){
			assert(confl_data.cnt_falsified_currentlvl == 0);
			for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]) {
				if (Level[-l] == decisionLevel()) confl_data.cnt_falsified_currentlvl++;
			}
		}
	}
	for(int x:confl_data.usedlist){
		varBumpActivity(x);
		if (confl_data.used[x] == 2) varBumpActivity(x);
	}
	for(int x:confl_data.usedlist)for(int l=-x;l<=x;l+=2*x)if(confl_data.M[l]){
		out_lits.push_back(l),out_coefs.push_back(min(confl_data.M[l],confl_data.w));
	}
	out_w=confl_data.w;
	confl_data.reset();
}

/**
 * Unit propagation with watched literals.
 * 
 * post condition: the propagation queue is empty (even if there was a conflict).
 */
CRef propagate() {
	CRef confl = CRef_Undef;
	while(qhead<(int)trail.size()){
		int p=trail[qhead++];
		Level[p] = decisionLevel();
		vector<Watch> & ws = adj[-p];
		vector<Watch>::iterator i, j, end;
		for(i = j = ws.begin(), end = ws.end(); i != end;){
			CRef cr = i->cref;
			i++;
			Clause & C = ca[cr];
			if(C.header.markedfordel)continue;
			int * lits = C.lits();
			int * coefs = C.coefs();
			bool watchlocked = false;
			for (int i=0; i<C.nwatch; i++) if (Level[-lits[i]] >= 0 && lits[i] != -p) watchlocked = true;
			if (!watchlocked) {
				int pos = 0; while (lits[pos] != -p) pos++;
				int c = coefs[pos];
				for(int it=C.nwatch;it<(int)C.size() && C.sumwatchcoefs-c < C.minsumwatch;it++)if(Level[-lits[it]]==-1){
					adj[lits[it]].push_back({cr});
					swap(lits[it],lits[C.nwatch]),swap(coefs[it],coefs[C.nwatch]);
					C.sumwatchcoefs += coefs[C.nwatch];
					C.nwatch++;
				}
				if (C.sumwatchcoefs-c >= C.minsumwatch) {
					swap(lits[pos],lits[C.nwatch-1]),swap(coefs[pos],coefs[C.nwatch-1]);
					C.sumwatchcoefs-=coefs[C.nwatch-1];
					C.nwatch--;
					continue;
				}
			}
			*j++ = {cr};
			long long s = slack(C.nwatch,lits,coefs,C.w);
			if(s<0){
				confl = cr;
				while (qhead < (int) trail.size()) Level[trail[qhead++]] = decisionLevel();
				while(i<end)*j++=*i++;
			}else{
				for(int it=0;it<C.nwatch;it++)if(Level[-lits[it]]==-1 && coefs[it] > s){
					NIMPL++;
					if (Level[lits[it]]==-1) {
						uncheckedEnqueue(lits[it], cr);
						NPROP++;
					}
				}
			}
		}
		ws.erase(j, end);
	}
	return confl;
}

inline bool LP_isActivated(){ return lpmulti!=0; }

int pickBranchLit(){
	int next = 0;

	// Activity based decision:
	while (next == 0 || Level[next] != -1 || Level[-next] != -1)
		if (order_heap.empty()){
			next = 0;
			break;
		}else
			next = order_heap.removeMax();

	if(next==0){
		return 0;
	}

	// Finally, decide the value (phase)
	if(LP_isActivated() && useLpPhase){
		if(lpPhase[next]!=phase[next]){
			NLPPHASEDIFF++;
		}
		return lpPhase[next];
	}
	return phase[next];
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Initialization
void init(){
	qhead = 0;
	ca.memory = NULL;
	ca.at = 0;
	ca.cap = 0;
	ca.wasted = 0;
	ca.capacity(1024*1024);//4MB
}

void setNbVariables(long long nvars){
	if (nvars < 0) exit_ERROR({"Number of variables must be positive."});
	if (nvars > 1e9) exit_ERROR({"Number of variables cannot exceet 1e9."});
	n = nvars;
	_adj.resize(2*n+1); adj = _adj.begin() + n;
	_Reason.resize(2*n+1, CRef_Undef); Reason = _Reason.begin() + n;
	_Level.resize(2*n+1); Level = _Level.begin() + n;
	phase.resize(n+1);
	lpPhase.resize(n+1);
	activity.resize(n+1);
	order_heap.init();
	for(int i=1;i<=n;i++){
		Level[i]=Level[-i]=-1;
		Reason[i]=Reason[-i]=CRef_Undef;
		phase[i]=-i;
		lpPhase[i]=-i;
		activity[i]=0;
		insertVarOrder(i);
		//adj[i].clear(); adj[-i].clear(); // is already cleared.
	}
	confl_data.init();
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Proto-constraint handling
void reduce_by_toplevel(vector<int>& lits, vector<int>& coefs, int& w){
	size_t i,j;
	for(i=j=0; i<lits.size(); i++){
		if(Level[ lits[i]]==0) w-=coefs[i]; else
		if(Level[-lits[i]]==0); else {
			lits[j]=lits[i];
			coefs[j]=coefs[i];
			j++;
		}
	}
	lits.erase(lits.begin()+j,lits.end());
	coefs.erase(coefs.begin()+j,coefs.end());
}

inline void saturate(vector<int>& coefs, int& w){
	for (int i = 0; i < (int) coefs.size(); i++) coefs[i] = min(coefs[i], w);
}

bool simplify_constraint(vector<int> &lits, vector<int> &coefs, int &w){
	reduce_by_toplevel(lits,coefs,w);
	if(w<=0) return true; // trivially satisfied constraint
	saturate(coefs,w); // as reduce_by_toplevel could have reduced w
	return false;
}

CRef learnConstraint(vector<int>& lits,vector<int>& coefs, int w, bool trivialLBD = false){
	assert(lits.size()>0);
	CRef cr = ca.alloc(lits,coefs,w, true);
	Clause & C = ca[cr];
	C.lbd = trivialLBD?n:computeLBD(cr);
	attachClause(cr);
	learnts.push_back(cr);
	if(w>1) ++NGENEREALPB;
	return cr;
}

void printConstraint(const vector<int>& lits, const vector<int>& coefs, int w){
	for(int i=0; i<lits.size(); ++i){
		std::cout << coefs[i] << "x" << lits[i] << " ";
	}
	std::cout << ">= " << w << std::endl;
}

bool testValidConstraint(const std::vector<int>& lits, const std::vector<int>& coeffs, int rhs){
	assert(lits.size()==coeffs.size());
	assert(lits.size()>0);
	assert(rhs>0);
	assert(rhs<=1e9);
	long long coeffsum=0;
	for(int i=0; i<lits.size(); ++i){
		coeffsum+=coeffs[i];
		assert(Level[lits[i]]!=0);
		assert(Level[-lits[i]]!=0);
		assert(coeffs[i]>0);
		assert(coeffs[i]<=rhs);
	}
	assert(coeffsum>=rhs);
	return true;
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
#include "lib/soplex/soplex.h"
soplex::SoPlex * lp_ptr;
bool foundLpSolution = false;
soplex::DVectorReal lpSolution;
soplex::DVectorReal lpSlackSolution;
soplex::DVectorReal lpMultipliers;
soplex::DVectorReal upperBounds;
soplex::DVectorReal lowerBounds;
soplex::DSVectorReal lpRow;
std::vector<int> datavec;

using bigint = __int128;
ostream& operator<<(ostream& os, const bigint& x){ os << (double) x; return os; }

inline soplex::SoPlex& getLP(){ return *lp_ptr; }

inline bool onTrail(int l){ return ~Level[l]; }
inline bool falsified(int l){ return onTrail(-l); }
inline bool assigned(int l){ return onTrail(l) || onTrail(-l); }

// NOTE: if b is positive, the comparison is more relaxed. If b is negative, the comparison is more strict.
inline bool relaxedLT(double a, double b){ return a <= b*(1+tolerance); }
// NOTE: if a is negative, the comparison is more relaxed. If a is positive, the comparison is more strict.
inline bool strictLT(double a, double b){ return !relaxedLT(b,a); }

inline double nonIntegrality(double a){ return abs(round(a)-a); }
inline bool validCoeff(double a){ return round(a)==a && abs(a)<=1e9; }
inline bool validRhs(double a){ return round(a)==a && a<=1e9 && a>=-1e15;} // variable normal form can have exceedingly small rhs

inline void LP_resetBasis(){
	++NLPRESETBASIS;
	getLP().clearBasis(); // and hope next iteration works fine
}

void LP_convertConstraint(CRef cr, soplex::DSVectorReal& row, long long& w){
	Clause& C = ca[cr];
	assert(row.max()==C.size());
	w = C.w;
	for (int i = 0; i < (int) C.size(); i++) {
		int l = C.lits()[i];
		int coef = C.coefs()[i];
		if (l < 0) {
			coef = -coef;
			w += coef;
		}
		row.add(abs(l), coef);
	}
	assert(validRhs(w));
}

void LP_addConstraints(const std::vector<CRef>& constrs){
	if(constrs.size()==0) return;
	soplex::LPRowSetReal allRows;
	allRows.reMax(constrs.size());
	for (CRef cr : constrs) { // all axioms
		assert(cr!=CRef_Undef && cr!=CRef_Unsat);
		assert(ca[cr].size()>0);
		soplex::DSVectorReal row(ca[cr].size());
		long long w;
		LP_convertConstraint(cr,row,w);
		allRows.add(soplex::LPRowReal(row, soplex::LPRowReal::Type::GREATER_EQUAL, w, 0));
	}
	getLP().addRowsReal(allRows);
	NLPCONSTR += constrs.size();
}

bool LP_pureCnf(){
	if(opt) return false;
	for(CRef cr: clauses) if(ca[cr].w>1)	return false;
	return true;
}

void LP_init() {
	if(LP_pureCnf()) {
		if (verbosity > 1) {
			std::cout << "c Problem is only clausal, disabling LP solving" << std::endl;
		}
		lpmulti = 0; // disables useless LP
		return; // only clausal constraints
	}

	if (verbosity > 1) {
		std::cout << "c Initializing LP" << std::endl;
	}
	lp_ptr = new soplex::SoPlex;
	lpSolution = soplex::DVectorReal(n + 1);
	lowerBounds.reDim(n + 1);
	upperBounds.reDim(n + 1);
	auto &lp = getLP();
	lp.setIntParam(soplex::SoPlex::SYNCMODE, soplex::SoPlex::SYNCMODE_ONLYREAL);
	lp.setIntParam(soplex::SoPlex::SOLVEMODE, soplex::SoPlex::SOLVEMODE_REAL);
	lp.setIntParam(soplex::SoPlex::CHECKMODE, soplex::SoPlex::CHECKMODE_REAL);
	lp.setIntParam(soplex::SoPlex::SIMPLIFIER, soplex::SoPlex::SIMPLIFIER_OFF);
	lp.setIntParam(soplex::SoPlex::OBJSENSE, soplex::SoPlex::OBJSENSE_MAXIMIZE);
	// Maximization ensures the objective constraint will be lower bounded, which corresponds to the PB objective
	// constraint, so we don't need to invert an objective constraint Farkas multiplier.
	lp.setIntParam(soplex::SoPlex::VERBOSITY, verbosity);
	// NOTE: alternative "crash basis" only helps on few instances, according to Ambros, so we don't adjust that parameter

	// first add variables
	// NOTE: batch version is more efficient than adding them one by one
	soplex::LPColSetReal allCols;
	allCols.reMax(n+1);
	soplex::DSVectorReal dummycol(0);
	for (int i = 0; i <= n; ++i) { // TODO: fix inefficient column 0, needed because SoPlex uses 0-based columns
		allCols.add(soplex::LPColReal(0, dummycol, 1, 0));
	}
	lp.addColsReal(allCols);

	// NOTE: batch version is more efficient than adding them one by one
	LP_addConstraints(clauses);

	// How does RoundingSat perform branch-and-bound minimization?
	// - F is the objective function, with a trivial lower bound L and trivial upper bound U
	// - let the rescaled upper bound be UU = 2^ceil(lg(U-L))
	// - take a set of auxiliary variables such that an exponentially weighted sum (EWS) over the negative (!)
	// literals of these variables represents some value Y s.t. 0 <= Y <= UU
	// - let the dynamically changing upper bound of F be UB = UU-Y
	// - introduce the constraint F-L =< UB = UU-Y
	// - flip the inequality: -F+L >= -UU+Y
	// - put -F-Y >= -UU-L in normal form
	// Now, if all auxiliary variables are true, Y==0, so only the trivial upper bound UU+L is enforced on F.
	// If all auxiliary variables are false, Y==UU, so F is forced on its trivial lower bound L.
	soplex::DVectorReal objective;
	objective.reDim(n + 1); // NOTE: automatically set to zero
	if(opt){ // add objective function
		Clause& o = ca[clauses[0]];
		soplex::DSVectorReal objRow(o.size());

		for(int i=0; i<o.size(); ++i){
			int c = o.coefs()[i];
			int v = o.lits()[i];
			if(abs(v)>n-opt_K) continue;
			if(v<0){
				v = -v;
				c = -c;
			}
			objective[v]=c;
			objRow.add(v,c);
		}
		lp.changeObjReal(objective);
		lp.changeRowReal(0,soplex::LPRowReal(-soplex::infinity, objRow, soplex::infinity));

		if(verbosity>1){
			lp.getObjReal(objective);
			std::cout << "c LP objective: ";
			for(int i=0; i<objective.dim(); ++i){
				double c = objective[i];
				if(c==0) continue;
				std::cout << c << "x" << i;
			}
			std::cout << std::endl;
		}
	}else{ // add default objective function
			for(int v=1; v<=n; ++v) objective[v]=-lpObjectiveCoef;
			getLP().changeObjReal(objective);
	}

	if (verbosity > 1) {
		std::cout << "c Finished initializing LP" << std::endl;
	}
}

template<class indexable> double LP_evalLhs(const indexable& lits, const indexable& coefs, int size){
	assert(foundLpSolution);
	double lhs = 0;
	for(int i=0; i<size; ++i){
		int l = lits[i];
		assert(abs(l)<lpSolution.dim());
		double lpval = lpSolution[abs(l)];
		lhs += (l>0?lpval:1-lpval)*coefs[i];
	}
	return lhs;
}

void LP_print(){
	std::cout << "LP: " << std::endl;
	soplex::DVectorReal slacks(getLP().numRowsReal());
	getLP().getSlacksReal(slacks);
	soplex::DVectorReal lpSolution(getLP().numColsReal());
	getLP().getPrimalReal(lpSolution);
	for(int i=0; i<getLP().numRowsReal(); ++i){
		lpRow.clear();
		getLP().getRowVectorReal(i,lpRow);
		std::cout << "r" << i << "=" << slacks[i] << ": " << getLP().lhsReal(i) << " =< ";
		for(int j=0; j<lpRow.size(); ++j){
			int v = lpRow.element(j).idx;
			std::cout << lpRow.element(j).val << "x" << v << "(" << lpSolution[v] << ")" <<
			(getLP().basisColStatus(v)==soplex::SPxSolver::VarStatus::BASIC?"* ":" ");
		}
		std::cout << " =< " << getLP().rhsReal(i) << std::endl;
	}
}

void LP_printInternals(){
	//LP_print();

	soplex::DVectorReal slacksSolution(getLP().numRowsReal());
	getLP().getSlacksReal(slacksSolution);
	soplex::DVectorReal lpSolution(getLP().numColsReal());
	getLP().getPrimalReal(lpSolution);

	std::cout << "Row-multiplied basis: " << std::endl;
	for(int i=0; i<getLP().numRowsReal(); ++i){
		double rhs = 0;
		std::vector<double> lhs;
		lhs.resize(getLP().numColsReal(),0);
		std::vector<double> slacks;
		slacks.resize(getLP().numRowsReal(),0);

		double xsum=0;
		std::cout << i << ": " << rhs << " =< ";
		for(int j=0; j<lhs.size(); ++j){
			if(abs(lhs[j]) == 0) continue;
			xsum+=lpSolution[j]*lhs[j];
			std::cout << lhs[j] << "x" << j;
			if(getLP().basisColStatus(j)==soplex::SPxSolver::VarStatus::BASIC){
				std::cout << "*";
			}
			std::cout << "[" << lpSolution[j] << "]";
			std::cout << " ";
		}
		std::cout << "= ";
		double ysum=0;
		for(int j=0; j<slacks.size(); ++j){
			if(abs(slacks[j]) == 0) continue;
			ysum+=slacksSolution[j]*slacks[j];
			std::cout << slacks[j] << "y" << j;
			if(getLP().basisRowStatus(j)==soplex::SPxSolver::VarStatus::BASIC){
				std::cout << "*";
			}
			std::cout << "[" << slacksSolution[j] << "]";
			std::cout << " ";
		}
		if(rhs > xsum || xsum!=ysum ){
			std::cout << " ERROR: " << rhs << "=<"<< xsum << "==" << ysum;
		}
		std::cout << std::endl;
	}
}

enum CutType { unsat, undef, gomory, farkas, dual, learned, farkas_uninstantiated }; // TODO: refactor away uninstantiated

struct CandidateCut{
	std::vector<std::pair<int,int> > coefflits;
	int degree;

	CutType type=CutType::undef;
	CRef cr=CRef_Undef;
	double lpViolation=0;
	double norm=-1;

	CandidateCut(const std::vector<int>& ls, const std::vector<int>& cs, int d, CutType t):degree(d),type(t),
			lpViolation(LP_evalLhs(ls,cs,ls.size()) - d){
		assert(ls.size()==cs.size());
		coefflits.reserve(ls.size());
		for(int i=0; i<ls.size(); ++i){
			int l = ls[i];
			int c = cs[i];
			coefflits.push_back({c,l});
		}
	}

	CandidateCut(CRef c, CutType t, double v):type(t),cr(c),degree(ca[c].w),lpViolation(v){
		Clause& C = ca[c];
		coefflits.reserve(C.size());
		for(int i=0; i<C.size(); ++i){
			int l = C.lits()[i];
			int c = C.coefs()[i];
			coefflits.push_back({c,l});
		}
	}

	CandidateCut(CutType t):type(t){}

	void calculateNormal(){
		assert(norm==-1);
		norm=0;
		for(int i=0; i<coefflits.size(); ++i){
			int lit = coefflits[i].second;
			int coef = coefflits[i].first;
			norm+=(double)coef*(double)coef;
			if(lit<0) coefflits[i]={-coef,-lit};
		}
		norm=sqrt(norm);
		assert(norm>0);
		lpViolation/=norm;
		sort(coefflits.begin(), coefflits.end(), [](const std::pair<int,int>& x, const std::pair<int,int>& y){
			return x.second<y.second;
		});
	}

	void resetNormal(){
		assert(norm!=-1); // so we need to convert back to normalized form
		for(std::pair<int,int>& cl: coefflits){
			int lit = cl.second;
			int coef = cl.first;
			if(cl.first<0) {
				cl.first = -cl.first;
				cl.second = -cl.second;
			}
		}
		norm=-1;
	}

	// @pre: litcoeffs is ordered and norm is calculated
	double cosOfAngleTo(const CandidateCut& other){
		assert(norm!=-1 && other.norm!=-1); // check whether norm is actually calculated and litcoeffs is ordered
		double cos = 0;
		int i=0; int j=0;
		while(i<coefflits.size() && j<other.coefflits.size()){
			int x=coefflits[i].second;
			int y=other.coefflits[j].second;
			if(x<y){
				++i;
			}else if(x>y){
				++j;
			}else{ // x==y
				cos+=(double)coefflits[i].first*(double)other.coefflits[j].first;
				++i;
				++j;
			}
		}
		return cos/(norm*other.norm);
	}

	void addAsLearned(){
		assert(norm==-1);
		std::vector<int> lits; lits.reserve(coefflits.size());
		std::vector<int> coefs; coefs.reserve(coefflits.size());
		for(const std::pair<int,int>& cl: coefflits){
			lits.push_back(cl.second);
			coefs.push_back(cl.first);
		}
		int w = degree;
		bool trivial = simplify_constraint(lits,coefs,w);
		_unused(trivial);
		assert(!trivial);
		cr = learnConstraint(lits, coefs, w, true);
	}

	bool violatesLpSolution(){
		return -lpViolation>tolerance;
	}

	bool violatesTrail(){
		long long result = -degree;
		for(int i=0; i<coefflits.size(); ++i){
			int l = coefflits[i].second;;
			int c = coefflits[i].first;;
			if(!falsified(l)) result+=c;
			if(result>=0) return false;
		}
		return true;
	}
};

/**
 * The following check assumes we want to minimize the measure coeffsum / rhs when weakening before rounding.
 *
 * Given the divisor div, the coeffsum sum, the degree rhs, and the remainder rem,
 * either the sum and the rhs will be decreased to sum-rem and rhs-rem (due to weakening),
 * or the sum will be increased to sum+div-rem (due to 'un'weakening).
 * We prefer to weaken when (sum-rem)/(rhs-rem) < (sum+div-rem)/rhs, which is equivalent to the implemented check.
 */
inline bool weakenDown(double div, double sum, double rhs, double rem){
	return rem*(sum + div) < rhs*div + rem*rem;
}

// NOTE: 2^59 is the maximum possible, given the 64 bits needed for other calculations
const long long maxMult = 576460752303423488; //2^50: 1125899906842624 | 2^55: 36028797018963968 | 2^59: 576460752303423488
const bigint maxMult_big = 1e37; // NOTE: std::numeric_limits<bigint>::max() did not work because of some reason

struct LinCombConstraint{
	bigint rhs;
	std::vector<bigint> _coeffs;
	std::vector<bigint>::iterator coeffs;
	// NOTE: useful to have coefficients for lits to easily use complementary variables in Gomory cut generation
	std::vector<bigint> row_coeffs;
	std::vector<int> lits;
	std::vector<int> coefs_res;
	int w_res;

	void reset(){
		_coeffs.resize(2*n+1,0);
		coeffs = _coeffs.begin()+n;
		row_coeffs.resize(getLP().numRowsReal());

		rhs = 0;
		w_res = 0;

		for(int l: lits){ coeffs[l]=0; }

		lits.clear();
		coefs_res.clear();

		for(int i=0; i<_coeffs.size(); ++i) assert(_coeffs[i]==0);
		for(int i=0; i<row_coeffs.size(); ++i) assert(row_coeffs[i]==0);
	}

	inline bool isNormalized(){
		if(rhs <= 0) return false;
		int nblits = 0;
		for(int l=-n; l<=n; ++l){
			if(coeffs[l]<0) return false;
			if(coeffs[l]>0) ++nblits;
		}
		return lits.size()==nblits;
	}

	// approximating double, as it is mainly used in heuristics and otherwise might risk integer overflow
	double getCoeffSum(){
		assert(isNormalized());
		double result = 0;
		for(int l: lits) result+=coeffs[l];
		return result;
	}

	// We don't need the exact value of a positive slack, so to avoid integer overflow,
	// stop calculating the slack if it is positive.
	bigint getSlack(){
		assert(isNormalized());
		bigint result = -rhs;
		for(int l: lits){
			if(result>=0) break;
			if(!falsified(l)) result+=coeffs[l];
		}
		return result;
	}

	bool isTriviallyInconsistent(){
		assert(isNormalized());
		bigint result = -rhs;
		for(int l: lits){
			if(result>=0) return false;
			result+=coeffs[l];
		}
		return result<0;
	}

	// BITWISE: +31 (max number of constraints in SoPlex is INT_MAX)
	void addScaledConstraint(bigint scale, int row){
		if(scale==0) return;
		if(opt && row==0 && getLP().lhsReal(0)==-soplex::infinity) return;

		assert(validRhs(getLP().lhsReal(row)));
		rhs+=((int) getLP().lhsReal(row))*scale;

		lpRow.clear();
		getLP().getRowVectorReal(row,lpRow);
		for(int i=0; i<lpRow.size(); ++i){
			const soplex::Nonzero<double>& el = lpRow.element(i);
			assert(validCoeff(el.val));
			bigint farkas_coeff = ((int) el.val)*scale;
			assert(farkas_coeff!=0);
			int x = el.idx;
			if(farkas_coeff<0){
				coeffs[-x]-=farkas_coeff;
				rhs-=farkas_coeff;
			}else{
				coeffs[x]+=farkas_coeff;
			}
		}
	}

	// saturates the constraint
	inline void saturate(){
		for(int l: lits) coeffs[l]=min(coeffs[l],rhs);
	}

	// BITWISE: +log2(maxMult)+log2(1e9)
	// @return: multiplier fitting in positive bigint range, s.t. multiplier*largestV <= maxMult
	double getScaleFactor(soplex::DVectorReal& v){
		// figure out greatest multiplier such that, for all i, v[i]*mult definitely fits in int32
		double largestV = maxMult/(double)maxMult_big;
		assert(maxMult/largestV<=maxMult_big);
		for(int i=0; i<v.dim(); ++i){
			if(isnan(v[i])) v[i]=0; // TODO: report this to Ambros?
			// NOTE: it is possible that v's multipliers are negative (e.g., when calculating Gomory cuts)
			if(abs(v[i])>largestV){ largestV = abs(v[i]); }
		}

		double mult = maxMult/largestV;
		assert(mult>0);
		assert(mult<=maxMult_big);
		return mult;
	}

	// BITWISE: -
	void convertToNormalForm(){
		// normalize this constraint (only one positive coefficient per literal), reduce level 0 literals
		for(int i=1; i<=n; ++i){
			int largest = i;
			if(coeffs[-largest]>coeffs[largest]){
				largest = -largest;
			}
			rhs-=coeffs[-largest];
			coeffs[largest]-=coeffs[-largest];
			coeffs[-largest]=0;

			if(Level[largest]==0){
				rhs-=coeffs[largest];
				coeffs[largest]=0;
			}else if(Level[-largest]==0){
				coeffs[largest]=0;
			}
		}

		// gather literals
		for(int l=-n; l<=n; ++l){
			assert(coeffs[l]>=0);
			if(coeffs[l]==0) continue;
			lits.push_back(l);
		}

		// saturate this constraint, compute slack and coefficient sum
		saturate();
	}

	CandidateCut getCandidateCut(CutType ct){
		if(rhs<=0) return CandidateCut(CutType::undef);
		if(isTriviallyInconsistent())	return CandidateCut(CutType::unsat);

		divideAndRound(0); // ensure coefficients are <= 1e9

		if(getSlack()<0 && decisionLevel()==0) {
			return CandidateCut(CutType::unsat);
		}else if(ct==CutType::farkas_uninstantiated) {
			return CandidateCut(CutType::farkas_uninstantiated);
		}else{
			return CandidateCut(lits,coefs_res,w_res,ct);
		}
	}

	// BITWISE: +1 for MIR coefficient calculation, +1 for readding rows after rounding
	CandidateCut createLinearCombinationGomory(soplex::DVectorReal& v){
		reset();
		assert(v.dim()>=getLP().numRowsReal());

		double mult = getScaleFactor(v);

		for (int j=0; j<v.dim(); ++j) {
			bigint farkas_mult = v[j]*mult;
			assert(abs(farkas_mult)<=maxMult);
			addScaledConstraint(farkas_mult,j);
			row_coeffs[j]=-farkas_mult;
		}

		double csum = 0;
		int nLits = 0;

		// normalize this constraint (only literal closest to 0 in LP solution), reduce level 0 literals
		for(int i=1; i<=n; ++i){
			int largest = i;
			if(lpSolution[i]>0.5){
				largest=-i;
			}

			rhs-=coeffs[-largest];
			coeffs[largest]-=coeffs[-largest];
			coeffs[-largest]=0;

			if(Level[largest]==0){
				rhs-=coeffs[largest];
				coeffs[largest]=0;
			}else if(Level[-largest]==0){
				coeffs[largest]=0;
			}

			if (coeffs[largest] != 0) {
				csum += abs(coeffs[largest]);
				++nLits;
			}
		}

		// use a sensible divisor to round with
		bigint divisor=(mult<2?2:mult);
		assert(divisor>0);

		// remove lits with very small coefficients
		double cutoff = csum*sanitizeFarkas/(double)nLits;
		for(int l=-n; l<=n; ++l){
			if(coeffs[l]==0 || abs(coeffs[l])>=cutoff) continue;
			if(coeffs[l]>0){ // weaken down
				rhs-=coeffs[l];
			} //else weaken up
			coeffs[l]=0;
		}
		bigint b = rhs;
		// round up the rhs MIR style
		rhs=mod_safe(b,divisor)*ceildiv_safe(b,divisor);
		// round up the coefficient MIR style
		for(int l=-n; l<=n; ++l){
			if(coeffs[l]==0) continue;
			coeffs[l]=mir_coeff(coeffs[l],b,divisor);
		}
		// round up the slack variables MIR style and cancel out the slack variables
		for(int i=0; i<row_coeffs.size(); ++i){
			bigint row_coeff=mir_coeff(row_coeffs[i],b,divisor);
			addScaledConstraint(row_coeff, i);
			row_coeffs[i] = 0;
		}

		convertToNormalForm();
		return getCandidateCut(CutType::gomory);
	}

	// BITWISE: -
	CandidateCut createLinearCombinationFarkas(soplex::DVectorReal& v, bool instantiate){
		reset();
		assert(v.dim()==getLP().numRowsReal());

		double mult = getScaleFactor(v);

		for (int j=0; j<v.dim(); ++j) {
			bigint farkas_mult = v[j]*mult;
			assert(abs(farkas_mult)<=maxMult);
			if(v[j]>0) addScaledConstraint(farkas_mult,j);
		}

		for(int l=-n; l<=n; ++l) assert(coeffs[l]>=0);

		convertToNormalForm();
		if(instantiate){
			return getCandidateCut(CutType::farkas);
		}else{
			return getCandidateCut(CutType::farkas_uninstantiated);
		}

	}

	// divisor==0: use smallest coefficient larger than cutoff as divisor
	// divisor==1: use smallest possible divisor to ensure coefficients <= 1e9
	// else: divisor is untouched, unless resulting coefficients are > 1e9
	// BITWISE: +1 (simple addition of 2 bigints)
	void divideAndRound(bigint divisor){
		assert(isNormalized());
		assert(divisor>=0);
		assert(test(false));

		// sort lits from highest coefficient to lowest, breaking ties on whether the literal is falsified
		std::sort(lits.begin(), lits.end(), [this](int a, int b) {
			return (this->coeffs[a] > this->coeffs[b] || (this->coeffs[a] == this->coeffs[b] && Level[-a] > Level[-b]));
		});
		assert(coeffs[lits[0]] >= coeffs[lits.back()]);

		double coeffSum = getCoeffSum();
		double cutoff = coeffSum/(double)lits.size()*sanitizeFarkas;

		if(divisor==0){ // find smallest coefficient larger than cutoff as divisor
			for(auto it=lits.rbegin(); it!=lits.rend(); ++it){
				divisor = coeffs[*it];
				if(divisor>cutoff) break;
			}
		}
		if(divisor>coeffs[lits.front()]) divisor = coeffs[lits.front()]; // avoid too large a divisor
		divisor = max(ceildiv(rhs,(bigint)1e9),divisor); // avoid too small a divisor
		assert(divisor>0);

		// Next, make sure any non-saturated coefficient is divisible by the divisor
		// NOTE: backward iteration serves to potentially eliminate small coefficient literals
		bigint negslack = getSlack();
		for(int i=lits.size()-1; i>=0; --i){
			int l = lits[i];
			bigint c = coeffs[l];
			if(c>=rhs) break; // all remaining coefficients are saturated
			bool falsified_l = falsified(l);

			// The following code handles small coefficient terms in the Farkas constraint. E.g.
			// 1x7 in 1000x1 1000x2 500x3 500x4 500x5 500x6 1x7 >= 2000
			if(c<cutoff && (negslack>=0 || negslack + c < 0 || !falsified_l)){
				negslack+=(falsified_l?c:0);
				coeffSum-=c;
				rhs-=c;
				coeffs[l]=0;
				aux::swapErase(lits,i);
				continue;
			}

			bigint remainder = c%divisor;
			bigint unremainder = divisor-remainder;
			if (falsified_l){
				if(weakenDown(divisor, coeffSum, rhs, remainder) && (negslack>=0 || negslack + remainder < 0)){
					// Weaken down:
					coeffs[l] -= remainder;
					coeffSum -= remainder;
					rhs -= remainder;
					negslack += remainder;
				}else{
					// Weaken up:
					coeffs[l] += unremainder;
					coeffSum += unremainder;
				}
			}else{
				if(!weakenDown(divisor, coeffSum, rhs, remainder) && (negslack>=0 || negslack + unremainder < 0)){
					// Weaken up:
					coeffs[l] += unremainder;
					coeffSum += unremainder;
					negslack += unremainder;
				}else{
					// Weaken down:
					coeffs[l] -= remainder;
					coeffSum -= remainder;
					rhs -= remainder;
				}
			}
			assert(coeffs[l] % divisor == 0);

			// do the actual division
			coeffs[l] /= divisor;
			if (coeffs[l] == 0) {
				aux::swapErase(lits, i);
			}
		}
		// NOTE: lits is no longer sorted, as some coefficients might be weakened up, and others weakened down

		rhs=ceildiv(rhs,divisor);

		saturate();

		// Now, all ceildiv(rhs,divisor) should fit within int range,
		// so the constraint is ready to be converted to 32 bit and added to the learnt constraint store.
		coefs_res.reserve(lits.size());
		for(int l: lits){
			assert(coeffs[l]>0);
			coefs_res.push_back(coeffs[l]);
		}
		assert(rhs>0);
		assert(rhs<=1e9);
		w_res = rhs;

		// printConstraint(lits,coefs_res,w_res);
		assert(testValidConstraint(lits,coefs_res,w_res));
		assert(test(true));
	}

	bool test(bool testRes){
		for(int l=-n+1; l<n; ++l) {
			if(coeffs[l]!=0) assert(aux::contains(lits,l));
		}

		assert(rhs>0);
		assert(!testRes ||rhs<=1e9);
		assert(lits.size()>0);
		assert(!testRes || w_res==rhs);

		for(int i=0; i<lits.size(); ++i){
			int l = lits[i];
			assert(coeffs[l]>0);
			assert(!testRes || coeffs[l]<=1e9);
			assert(coeffs[-l]==0);
			assert(!testRes || coefs_res[i]==coeffs[l]);
		}

		return true;
	}

	void print(){
		for(int l: lits){
			std::cout << coeffs[l] << "x" << l << "|" << (falsified(l)?"F":(falsified(-l)?"T":"U")) << " ";
		}
		std::cout << ">= " << rhs << " (" << (double) getSlack() << ")" << endl;
	}

	void printGomory(){
		soplex::DVectorReal lpSlackSolution(getLP().numRowsReal());
		getLP().getSlacksReal(lpSlackSolution);
		// double eval = -rhs;
		double eval = 0;
		for(int l=-n; l<=n; ++l){
			if(coeffs[l]==0) continue;
			double sol = (l<0?(1-lpSolution[-l]):lpSolution[l]);
			eval+=coeffs[l]*sol;
			std::cout << coeffs[l] << "x" << l << "(" << sol << ")" <<
        (getLP().basisColStatus(abs(l))==soplex::SPxSolver::VarStatus::BASIC?"* ":" ");
		}
		std::cout << ">= ";
		for(int i=0; i<row_coeffs.size(); ++i){
			if(row_coeffs[i]==0) continue;
			eval-=row_coeffs[i]*lpSlackSolution[i];
			std::cout << row_coeffs[i] << "y" << i << "(" << lpSlackSolution[i] << ")" <<
				(getLP().basisRowStatus(i)==soplex::SPxSolver::VarStatus::BASIC?"* ":" ");
		}
		std::cout << rhs << " [" << eval << "]" << std::endl;
	}
} lcc;

std::pair<CRef,soplex::SPxSolver::Status> LP_run(bool cutInternal=true){
	// Set the  LP's bounds based on the current trail
	for (int i=1; i<=n; i++) {
		lowerBounds[i] = 0;
		upperBounds[i] = 1;
		if (onTrail(i)) lowerBounds[i] = 1;
		if (onTrail(-i)) upperBounds[i] = 0;
	}
	getLP().changeBoundsReal(lowerBounds, upperBounds);

	// Run the LP
	soplex::SPxSolver::Status stat;
	stat = getLP().optimize();
	++NLPCALLS;
	NLPPIVOTS+=getLP().numIterations();
	LPSOLVETIME+=getLP().solveTime();

	if(verbosity>1){
		std::cout << "c LP status: " << stat << std::endl;
	}
	assert(stat != soplex::SPxSolver::Status::NO_PROBLEM);
	assert(stat <= soplex::SPxSolver::Status::OPTIMAL_UNSCALED_VIOLATIONS);
	assert(stat >= soplex::SPxSolver::Status::ERROR);

	if(stat == soplex::SPxSolver::Status::ABORT_ITER) return {CRef_Undef,stat};

	if (stat == soplex::SPxSolver::Status::OPTIMAL) {
		++NLPOPTIMAL;
		if(getLP().numIterations()==0){ ++NLPNOPIVOT; return {CRef_Undef,stat}; } // no use calculating solution if it is not changed
		if(!getLP().hasSol()){ ++NLPNOPRIMAL; LP_resetBasis(); return {CRef_Undef,stat}; }

		if(cutInternal && useInternalOptimality){
			getLP().getPrimalReal(lpSolution);
			foundLpSolution = true;
			if(useLpPhase) for (int i = 1; i <= n; ++i) lpPhase[i] = (lpSolution[i]<=0.5)?-i:i;
			lpSlackSolution.reDim(getLP().numRowsReal());
			getLP().getSlacksReal(lpSlackSolution);

			auto& indices = datavec;
			indices.resize(getLP().numRowsReal());
			getLP().getBasisInd(indices.data());
			lpMultipliers.reDim(getLP().numRowsReal());
			double maxFractionality=0;
			int mostFractionalRow=-1;
			for(int row=0; row<getLP().numRowsReal(); ++row){
				double fractionality=0;
				if(indices[row]>=0){ // basic original variable / column
					fractionality = nonIntegrality(lpSolution[indices[row]]);
				}else{ // basic slack variable / row
					fractionality = nonIntegrality(lpSlackSolution[-indices[row]-1]);
				}
				if(fractionality>maxFractionality){
					maxFractionality=fractionality;
					mostFractionalRow=row;
				}
				if(maxFractionality==0.5) break;
			}

			if(maxFractionality>tolerance){
				getLP().getBasisInverseRowReal(mostFractionalRow,lpMultipliers.get_ptr());

				CandidateCut cut = lcc.createLinearCombinationGomory(lpMultipliers);
				if(cut.type==CutType::unsat){
					++NLPGOMORYCUTSINTERNAL;
					++NLPGOMORYCUTSINTERNALINFEASIBLE;
					return {CRef_Unsat,soplex::SPxSolver::Status::INFEASIBLE};
				}	else if(cut.type!=CutType::undef && cut.violatesTrail()) {
					++NLPGOMORYCUTSINTERNAL;
					++NLPGOMORYCUTSINTERNALINFEASIBLE;
					cut.addAsLearned();
					if(cut.violatesLpSolution()) LP_addConstraints({cut.cr});
					return {cut.cr, soplex::SPxSolver::Status::INFEASIBLE};
				} else if(cut.type!=CutType::undef && cut.violatesLpSolution()){
					++NLPGOMORYCUTSINTERNAL;
					cut.addAsLearned();
					LP_addConstraints({cut.cr});
					return {CRef_Undef,soplex::SPxSolver::Status::OPTIMAL};
				}

				for(int i=0; i<lpMultipliers.dim(); ++i) lpMultipliers[i]=-lpMultipliers[i];
				cut = lcc.createLinearCombinationGomory(lpMultipliers);
				if(cut.type==CutType::unsat){
					++NLPGOMORYCUTSINTERNAL;
					++NLPGOMORYCUTSINTERNALINFEASIBLE;
					return {CRef_Unsat,soplex::SPxSolver::Status::INFEASIBLE};
				}	else if(cut.type!=CutType::undef && cut.violatesTrail()) {
					++NLPGOMORYCUTSINTERNAL;
					++NLPGOMORYCUTSINTERNALINFEASIBLE;
					cut.addAsLearned();
					if(cut.violatesLpSolution()) LP_addConstraints({cut.cr});
					return {cut.cr, soplex::SPxSolver::Status::INFEASIBLE};
				} else if(cut.type!=CutType::undef && cut.violatesLpSolution()){
					++NLPGOMORYCUTSINTERNAL;
					cut.addAsLearned();
					LP_addConstraints({cut.cr});
					return {CRef_Undef,soplex::SPxSolver::Status::OPTIMAL};
				}
			}
		}

		return {CRef_Undef,soplex::SPxSolver::Status::OPTIMAL};
	}

	if(stat == soplex::SPxSolver::Status::ABORT_CYCLING){ ++NLPCYCLING; LP_resetBasis(); return {CRef_Undef,stat}; }
	if(stat == soplex::SPxSolver::Status::SINGULAR) { ++NLPSINGULAR; LP_resetBasis(); return {CRef_Undef,stat}; }
	if(stat != soplex::SPxSolver::Status::INFEASIBLE) { ++NLPOTHER; LP_resetBasis(); return {CRef_Undef,stat}; }

	// Infeasible LP :)
	AVGLPINFEASDEPTH=(AVGLPINFEASDEPTH*NLPINFEAS+decisionLevel())/(double) (NLPINFEAS+1);
	++NLPINFEAS;

	// To prove that we have an inconsistency, let's build the Farkas proof
	if(!getLP().hasDualFarkas()){
		++NLPNOFARKAS;
		LP_resetBasis();
		return {CRef_Undef,soplex::SPxSolver::Status::INFEASIBLE};
	}

	// extract the Farkas multipliers from the LP as positive big ints
	lpMultipliers.reDim(getLP().numRowsReal());
	getLP().getDualFarkasReal(lpMultipliers);

	CandidateCut cut = lcc.createLinearCombinationFarkas(lpMultipliers,false);
	if(cut.type==CutType::undef){
		LP_resetBasis();
		return {CRef_Undef,soplex::SPxSolver::Status::INFEASIBLE};
	}else if(cut.type==CutType::unsat){
		++NLPFARKAS;
		return {CRef_Unsat,soplex::SPxSolver::Status::INFEASIBLE};
	}else {
		assert(cut.type==CutType::farkas_uninstantiated);
		CRef cr = learnConstraint(lcc.lits,lcc.coefs_res,lcc.w_res);
		claBumpActivity(ca[cr]);
		if(lcc.getSlack()<0){
			++NLPFARKAS;
			return {cr, soplex::SPxSolver::Status::INFEASIBLE};
		}else{
			return {CRef_Undef, soplex::SPxSolver::Status::INFEASIBLE}; // don't use it to backjump
		}
	}
}

inline int LP_getAllowedPivots(){
	// explanation of formula:
	// start at 1 to allow initial LP search
	// allow as many (total) pivots as weighted conflict count
	// subtract total pivots so far
	// each call to LP solver also counts as a pivot, to reduce number of feasibility calls (that have 0 pivot count)
	return ceil(lpmulti*(1+NCONFL)-NLPPIVOTS-NLPCALLS);
}

CRef LP_tryRun(){
	if(lpmulti>=0){
		int allowed = LP_getAllowedPivots();
		if(allowed<=0){ // no pivot budget available
			return CRef_Undef;
		}else{ // limit number of pivots
			getLP().setIntParam(soplex::SoPlex::ITERLIMIT, allowed+100);
			// NOTE: when triggered, allow the LP at least 100 pivots to run.
			// This value is conservative: in benchmarks, SCIP has 382 (median) and 1391 (average) pivots / soplex call.
		}
	} // else, no pivot limit

	return LP_run().first;
}

void LP_printConstraint(CRef cr){
	if(cr==CRef_Undef){ std::cout << "?" << std::endl; return; }
	if(cr==CRef_Unsat){ std::cout << "0>=1" << std::endl; return; }
	Clause & C = ca[cr];
	double lhs = 0;
	for(int i=0; i<C.size(); ++i){
		int l=C.lits()[i];
		double lpval = lpSolution[abs(l)];
		lhs += (l>0?lpval:1-lpval)*C.coefs()[i];
		std::cout << C.coefs()[i] << "x" << l << ":" << lpval << " ";
	}
	std::cout << ">= " << C.w << ":" << lhs << std::endl;
}

void LP_deleteCuts(){
	assert(getLP().numRowsReal()>=clauses.size());
	if(!foundLpSolution) return;

	lpMultipliers.reDim(getLP().numRowsReal());
	getLP().getDualReal(lpMultipliers);

	auto& rowsToRemove=datavec;
	rowsToRemove.resize(getLP().numRowsReal());
	for(int i=0; i<clauses.size(); ++i) rowsToRemove[i]=0; // keep original constraints
	for(int i=clauses.size(); i<rowsToRemove.size(); ++i) {
		if(lpMultipliers[i]!=0){
			rowsToRemove[i]=0; // keep it
		}else{
			rowsToRemove[i]=-1; // erase it
			++NLPDELETEDCUTS;
		}
	}
	getLP().removeRowsReal(rowsToRemove.data());
}

void LP_learnCuts(std::vector<CandidateCut>& cuts, int maxAllowed){
	if(!foundLpSolution) return;
	int maxSize = cuts.size()+maxAllowed;
	for(auto cr: learnts){
		assert(cr!=CRef_Unsat);
		assert(cr!=CRef_Undef);
		Clause& C = ca[cr];
		double evalLhs = LP_evalLhs(C.lits(),C.coefs(),C.size());
		if(strictLT(evalLhs,C.w)){
			cuts.push_back(CandidateCut(cr,CutType::learned,evalLhs-C.w));
			if(cuts.size()>=maxSize) break;
		}
	}
}

bool LP_addGomoryCuts(std::vector<CandidateCut>& cuts, int maxAllowed){ // returns false if empty constraint detected
	assert(decisionLevel()==0); // otherwise we might generate cuts conflicting with the current trail
	assert(LP_isActivated());

	int maxSize = cuts.size()+maxAllowed;
	std::vector<std::pair<double,int> > fractionality2row;
	auto& indices = datavec;
	indices.resize(getLP().numRowsReal());
	getLP().getBasisInd(indices.data());
	lpMultipliers.reDim(getLP().numRowsReal());

	for(int row=0; row<getLP().numRowsReal(); ++row) {
		double fractionality = 0;
		if (indices[row] >= 0) { // basic original variable / column
			fractionality = nonIntegrality(lpSolution[indices[row]]);
		} else { // basic slack variable / row
			fractionality = nonIntegrality(lpSlackSolution[-indices[row] - 1]);
		}
		if (fractionality <= tolerance) continue;

		// The row is fractional
		fractionality2row.push_back({fractionality,row});
	}

	sort(fractionality2row.begin(), fractionality2row.end(), [](std::pair<double,int>& x,std::pair<double,int>& y){return x.first>y.first;});

	for(std::pair<double,int>& f2r: fractionality2row){

		getLP().getBasisInverseRowReal(f2r.second,lpMultipliers.get_ptr());

		CandidateCut cut = lcc.createLinearCombinationGomory(lpMultipliers);
		if(cut.type==CutType::unsat){ ++NLPGOMORYCUTS; return false; }
		else if(cut.type!=CutType::undef && cut.violatesLpSolution()){
			cuts.push_back(cut);
		}

		for(int i=0; i<lpMultipliers.dim(); ++i) lpMultipliers[i]=-lpMultipliers[i];
		cut = lcc.createLinearCombinationGomory(lpMultipliers);
		if(cut.type==CutType::unsat){ ++NLPGOMORYCUTS; return false; }
		else if(cut.type!=CutType::undef && cut.violatesLpSolution()){
			cuts.push_back(cut);
		}

		if(cuts.size()>=maxSize) break;
	}

	// TODO: if a cut is propagating or conflicting, we expect the two-watched literal scheme to pick this up
	return true;
}

bool LP_addDualCuts(std::vector<CandidateCut>& cuts){
	assert(getLP().hasSol());

	lpMultipliers.reDim(getLP().numRowsReal());
	getLP().getDualReal(lpMultipliers);

	CandidateCut cut = lcc.createLinearCombinationGomory(lpMultipliers);
	// NOTE: cuts not violating the LP solution might be useful as learned constraint
	if(cut.type==CutType::unsat){ ++NLPDUALCUTS; return false; }
	else if(cut.type!=CutType::undef){
		if(cut.violatesLpSolution()){
			cut.type=CutType::dual;
			cuts.push_back(cut);
		}
	}

	cut = lcc.createLinearCombinationFarkas(lpMultipliers,true);
	if(cut.type==CutType::unsat){ ++NLPDUALCUTS; return false; }
	else if(cut.type!=CutType::undef){
		if(cut.violatesLpSolution()){
			cut.type=CutType::dual;
			cuts.push_back(cut);
		}
	}

	return true;
}

CRef LP_inProcess(){
	backjumpTo(0); // NOTE: LP_run() makes use of the trail at multiple points

	getLP().setIntParam(soplex::SoPlex::ITERLIMIT, -1);

	std::pair<CRef,soplex::SPxSolver::Status> result = LP_run(false); // TODO: what happens with the auxiliary optimization variables?
	if(result.second!=soplex::SPxSolver::Status::OPTIMAL){
		// NOTE: status can be soplex::SPxSolver::Status::OPTIMAL_UNSCALED_VIOLATIONS, pointing to something fishy in SoPlex
		// Treat this as an error, not as an optimality!
		std::cout << "c LP status: " << result.second << std::endl;
		assert(result.second!=soplex::SPxSolver::Status::NO_PROBLEM);
		return result.first;
	}
	assert(result.first==CRef_Undef);
	assert(result.second==soplex::SPxSolver::Status::OPTIMAL);

	double time = cpuTime();

	getLP().getPrimalReal(lpSolution);
	foundLpSolution = true;
	if(useLpPhase) for (int i = 1; i <= n; ++i) lpPhase[i] = (lpSolution[i]<=0.5)?-i:i;
	lpSlackSolution.reDim(getLP().numRowsReal());
	getLP().getSlacksReal(lpSlackSolution);
	double objValue = getLP().objValueReal(); // NOTE: store this value, as it disappears after adding/removing rows

	std::vector<CandidateCut> cutList;
	// NOTE: LP_deleteCuts only deletes not weakly tight constraints, LP_learnCuts only adds strongly tight constraints.
	// Hence, there should be no overlap between the constraints considered by the two methods.
	// NOTE: LP_learnCuts does not modify the LP solver state, so it is safe to call before LP_adGomoryCuts
	// Also, to avoid adding gomory cuts twice to the LP solver, LP_learnCuts should be called before LP_adGomoryCuts
	if(learnCuts) LP_learnCuts(cutList,2*cutRoundLimit);
	// NOTE: no constraints can be added between LP call and addGomoryCuts (inclusive), as otherwise the basis indices
	// might point to new rows, which do not yet have a slack variable assignment in lpSlackSolution.
	// NOTE: should come after LP_learnCuts, as otherwise the cuts might be added twice.
	if(addGomoryCuts) if(!LP_addGomoryCuts(cutList,2*cutRoundLimit)){
		LPCUTTIME += cpuTime()-time;
		return CRef_Unsat;
	}
	// NOTE: should come after LP_learnCuts, as otherwise the cuts might be added twice.
	if(addDualCuts) if(!LP_addDualCuts(cutList)){
		LPCUTTIME += cpuTime()-time;
		return CRef_Unsat;
	}
	// first, delete all non-tight previously added constraints
	// NOTE: deleteCuts modifies state of LP object, so we must run LP_addGomoryCuts and LP_addDualCuts first.
	if(deleteCuts) LP_deleteCuts();

	// filter the collected cuts heuristically
	for(CandidateCut& cc: cutList) cc.calculateNormal();
	// NOTE: lpviolations are negative, so the smaller, the higher its absolute value
	sort(cutList.begin(), cutList.end(), [](const CandidateCut& x, const CandidateCut& y){
		return x.lpViolation<y.lpViolation || (x.lpViolation==y.lpViolation && x.coefflits.size()<y.coefflits.size());
	});
	std::vector<int> filteredCuts; // indices in cutList
	filteredCuts.reserve(max(10,cutRoundLimit));
	for(int i=0; i<cutList.size(); ++i){
		CandidateCut& pc = cutList[i];

		for(int j: filteredCuts){
			if(pc.cosOfAngleTo(cutList[j])>maxCutCos){
				goto skipCut;
			}
		}
		filteredCuts.push_back(i);

skipCut:
		if(filteredCuts.size()>=cutRoundLimit) break;
	}

	// add the filtered cuts to the LP
	std::vector<CRef> filteredCrefs;
	filteredCrefs.reserve(filteredCuts.size());
	for(int j: filteredCuts){
		CandidateCut& pc = cutList[j];
		switch(pc.type){
			case CutType::gomory:
				pc.resetNormal();
				pc.addAsLearned();
				++NLPGOMORYCUTS;
				break;
			case CutType::dual:
				pc.resetNormal();
				pc.addAsLearned();
				++NLPDUALCUTS;
				break;
			case CutType::learned:
				// NOTE: already present as learned constraint
				++NLPLEARNEDCUTS;
				break;
			default:
				assert(false);
				break;
		}

		CRef cr = pc.cr;
		filteredCrefs.push_back(cr);
		claBumpActivity(ca[cr]); // bump added constraints once
	}
	LP_addConstraints(filteredCrefs);

	LPCUTTIME += cpuTime()-time;
	std::cout <<
	          "c LP objective: " << -objValue <<
	          " [CUTS] dual: " << NLPDUALCUTS <<
	          " learned: " << NLPLEARNEDCUTS <<
	          " gomory: " << NLPGOMORYCUTS <<
	          " deleted: " << NLPDELETEDCUTS <<
	          " farkas: " << NLPFARKAS <<
	          " time: " << LPCUTTIME <<
	          std::endl;

	return CRef_Undef;
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// Parsers
void addConstraint(Constraint<int, long long>& c){
	std::vector<int> lits; std::vector<int> coefs; long long d=0; int w;
	c.getNormalForm(lits,coefs,d);
	if (abs(d) > (long long) 1e9) exit_ERROR({"Normalization of an input constraint causes degree to exceed 10^9."});
	w=(int)d;
	bool trivial = simplify_constraint(lits,coefs,w);
	if(trivial) return; // already satisfied.
	long long som = 0;for(int c:coefs)som+=c;
	if(som < w)puts("c UNSAT trivially inconsistent constraint"),exit_UNSAT();
	for(size_t i=0;i<lits.size();i++)if(som-coefs[i] < w){
		//printf("propagate %d\n",lits[i]);
		uncheckedEnqueue(lits[i],CRef_Undef);
	}
	if(trivial) return; // already satisfied.
	CRef cr = ca.alloc(lits, coefs, w, false);
	attachClause(cr);
	clauses.push_back(cr);
	if (propagate() != CRef_Undef)puts("c UNSAT initial conflict"),exit_UNSAT();
}

/*
 * The OPB parser does not support nonlinear constraints like "+1 x1 x2 +1 x3 x4 >= 1;"
 */
int read_number(const string & s) {
	long long answer = 0;
	for (char c : s) if ('0' <= c && c <= '9') {
		answer *= 10, answer += c - '0';
		if (answer > (int) 1e9) exit_ERROR({"Input formula contains absolute value larger than 10^9: ",s});
	}
	for (char c : s) if (c == '-') answer = -answer;
	return answer;
}

void addObjective(Constraint<int, long long>& c) {
	assert(clauses.size()==0); // objective function bound must be first constraint
	std::vector<int> lits; std::vector<int> coefs;
	for(int v: c.vars) if(c.coefs[v]!=0) {
		lits.push_back(v);
		coefs.push_back(c.coefs[v]);
	}
	opt = true;
	opt_coef_sum = 0;
	opt_normalize_add = 0;
	for(size_t i=0;i<lits.size();i++){
		if(coefs[i] < 0) lits[i]*=-1,coefs[i]*=-1,opt_normalize_add+=coefs[i];
		opt_coef_sum+=coefs[i];
		lits[i]=-lits[i];
		if (opt_coef_sum > (int) 1e9) exit_ERROR({"Sum of coefficients in objective function exceeds 10^9."});
	}
	opt_K = 0; while ((1<<opt_K) <= opt_coef_sum) opt_K++;
	for(int i=0;i<opt_K;i++)lits.push_back(n+1+i),coefs.push_back(1<<i);
	setNbVariables(n+opt_K);
	CRef cr = CRef_Undef;
	if(lits.size()==0) { // Trivial objective function.
		// Add dummy objective, as it is assumed the objective function is stored as first constraint.
		cr = ca.alloc({0, 0}, {0, 0}, 0, false);
	}else{
		cr = ca.alloc(lits, coefs, opt_coef_sum, false);
	}
	attachClause(cr);
	clauses.push_back(cr);
}

void opb_read(istream & in) {
	bool first_constraint = true;
	_unused(first_constraint);
	for (string line; getline(in, line);) {
		if (line.empty()) continue;
		else if (line[0] == '*') continue;
		else {
			for (char & c : line) if (c == ';') c = ' ';
			bool opt_line = line.substr(0, 4) == "min:";
			string line0;
			if (opt_line) line = line.substr(4), assert(first_constraint);
			else {
				string symbol;
				if (line.find(">=") != string::npos) symbol = ">=";
				else symbol = "=";
				assert(line.find(symbol) != string::npos);
				line0 = line;
				line = line.substr(0, line.find(symbol));
			}
			first_constraint = false;
			istringstream is (line);
			tmpConstraint.reset();
			vector<string> tokens;
			{ string tmp; while (is >> tmp) tokens.push_back(tmp); }
			if (tokens.size() % 2 != 0) exit_ERROR({"No support for non-linear constraints."});
			for (int i=0; i<(int)tokens.size(); i+=2) if (find(tokens[i].begin(),tokens[i].end(),'x')!=tokens[i].end()) exit_ERROR({"No support for non-linear constraints."});
			for (int i=0; i<(int)tokens.size(); i+=2) {
				string scoef = tokens[i];
				string var = tokens[i+1];
				int coef = read_number(scoef);
				bool negated = false;
				string origvar = var;
				if (!var.empty() && var[0] == '~') {
					negated = true;
					var = var.substr(1);
				}
				if (var.empty() || var[0] != 'x') exit_ERROR({"Invalid literal token: ",origvar});
				var = var.substr(1);
				int l = atoi(var.c_str());
				if (!(1 <= l && l <= n)) exit_ERROR({"Literal token out of variable range: ",origvar});
				if (negated) l = -l;
				tmpConstraint.addLhs(coef,l);
			}
			if (opt_line) addObjective(tmpConstraint);
			else {
				tmpConstraint.addRhs(read_number(line0.substr(line0.find("=") + 1)));
				addConstraint(tmpConstraint);
				// Handle equality case with two constraints
				if (line0.find(" = ") != string::npos) {
					tmpConstraint.invert();
					addConstraint(tmpConstraint);
				}
			}
		}
	}
}

void wcnf_read_objective(istream & in, long long top) {
	std::vector<int> weights;
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			istringstream is (line);
			long long weight; is >> weight;
			if(weight>=top) continue; // hard clause
			if(weight>1e9) exit_ERROR({"Clause weight exceeds 10^9: ",std::to_string(weight)});
			if(weight<0) exit_ERROR({"Negative clause weight: ",std::to_string(weight)});
			if(weight==0){
				std::cout << "c Warning: ignoring clause with weight 0" << std::endl;
			}else{
				weights.push_back(weight);
			}
		}
	}
	nbWcnfAuxVars = weights.size();
	tmpConstraint.reset();
	for(int i=0; i<nbWcnfAuxVars; ++i) tmpConstraint.addLhs(weights[i],n+1+i);
	setNbVariables(n+nbWcnfAuxVars);
	addObjective(tmpConstraint);
}

void wcnf_read(istream & in, long long top) {
	int auxvar = getNbOrigVars();
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			istringstream is (line);
			long long weight; is >> weight;
			if(weight==0) continue;
			tmpConstraint.reset();
			tmpConstraint.addRhs(1);
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			if(weight<top){ // soft clause
				++auxvar;
				tmpConstraint.addLhs(1,auxvar);
			} // else hard clause
			addConstraint(tmpConstraint);
		}
	}
}

void cnf_read(istream & in) {
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		else {
			istringstream is (line);
			tmpConstraint.reset();
			tmpConstraint.addRhs(1);
			int l;
			while (is >> l, l) tmpConstraint.addLhs(1,l);
			addConstraint(tmpConstraint);
		}
	}
}

void file_read(istream & in) {
	for (string line; getline(in, line);) {
		if (line.empty() || line[0] == 'c') continue;
		if (line[0] == 'p') {
			istringstream is (line);
			is >> line; // skip 'p'
			string type; is >> type;
			int n; is >> n;
			setNbVariables(n);
			if(type=="cnf"){
			  cnf_read(in);
			  return;
			}else if(type == "wcnf"){
				is >> line; // skip nbConstraints
				long long top; is >> top;
				// NOTE: keeping formula in memory because I need a dual pass to first extract the auxiliary variables,
				// and later extract the (potentially soft) constraints
				std::string formula{ std::istreambuf_iterator<char>(in),
				                     std::istreambuf_iterator<char>() };
				istringstream in2(formula);
			  wcnf_read_objective(in2,top);
			  istringstream in3(formula);
			  wcnf_read(in3,top);
			  return;
			}
		} else if (line[0] == '*' && line.substr(0, 13) == "* #variable= ") {
			istringstream is (line.substr(13));
			int n;
			is >> n;
			setNbVariables(n);
			opb_read(in);
			return;
		}
	}
	exit_ERROR({"No supported format [opb, cnf, wcnf] detected."});
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
// We assume in the garbage collection method that reduceDB() is the
// only place where clauses are deleted.
void garbage_collect(){
	if (verbosity > 0) puts("c GARBAGE COLLECT");
	for(int l=-n; l<=n; l++) {
		size_t i, j;
		for(i=0,j=0;i<adj[l].size();i++){
			CRef cr = adj[l][i].cref;
			if(!ca[cr].markedfordel())adj[l][j++]=adj[l][i];
		}
		adj[l].erase(adj[l].begin()+j,adj[l].end());
	}
	// clauses, learnts, adj[-n..n], reason[-n..n].
	uint32_t ofs_learnts=0;for(CRef cr:clauses)ofs_learnts+=ca.sz_clause(ca[cr].size());
	sort(learnts.begin(), learnts.end(), [](CRef x,CRef y){return x.ofs<y.ofs;}); // we have to sort here, because reduceDB shuffles them.
	ca.wasted=0;
	ca.at=ofs_learnts;
	vector<CRef> learnts_old = learnts;
	for(CRef & cr : learnts){
		size_t length = ca[cr].size();
		memmove(ca.memory+ca.at, ca.memory+cr.ofs, sizeof(uint32_t)*ca.sz_clause(length));
		cr.ofs = ca.at;
		ca.at += ca.sz_clause(length);
	}
	#define update_ptr(cr) if(cr.ofs>=ofs_learnts)cr=learnts[lower_bound(learnts_old.begin(), learnts_old.end(), cr)-learnts_old.begin()]
	for(int l=-n; l<=n; l++)for(size_t i=0;i<adj[l].size();i++)update_ptr(adj[l][i].cref);
	for(int l=-n;l<=n;l++)if(Reason[l]!=CRef_Undef)update_ptr(Reason[l]);
	#undef update_ptr
}

struct reduceDB_lt {
    bool operator () (CRef x, CRef y) { 
 
    // Main criteria... Like in MiniSat we keep all binary clauses
    if(ca[x].size()> 2 && ca[y].size()==2) return 1;
    
    if(ca[y].size()>2 && ca[x].size()==2) return 0;
    if(ca[x].size()==2 && ca[y].size()==2) return 0;
    
    // Second one  based on literal block distance
    if(ca[x].lbd> ca[y].lbd) return 1;
    if(ca[x].lbd< ca[y].lbd) return 0;    
    
    
    // Finally we can use old activity or size, we choose the last one
        return ca[x].act < ca[y].act;
	//return x->size() < y->size();

        //return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
    }    
};
void reduceDB(){
	size_t i, j;

	sort(learnts.begin(), learnts.end(), reduceDB_lt());
	if(ca[learnts[learnts.size() / 2]].lbd<=3) nbclausesbeforereduce += 1000;
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	for (i = j = 0; i < learnts.size(); i++){
		Clause& c = ca[learnts[i]];
		if (c.lbd>2 && c.size() > 2 && !locked(learnts[i]) && i < learnts.size() / 2){
      removeClause(learnts[i]);
		}else{
			learnts[j++] = learnts[i];
		}
	}
	learnts.erase(learnts.begin()+j,learnts.end());
	if ((double) ca.wasted / (double) ca.at > 0.2) garbage_collect();
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------
static double luby(double y, int x){

	// Find the finite subsequence that contains index 'x', and the
	// size of that subsequence:
	int size, seq;
	for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

	while (size-1 != x){
		size = (size-1)>>1;
		seq--;
		x = x % size;
	}

	return pow(y, seq);
}

// ---------------------------------------------------------------------
// ---------------------------------------------------------------------

bool asynch_interrupt = false;
static void SIGINT_interrupt(int signum){
	asynch_interrupt = true;
}

static void SIGINT_exit(int signum){
	printf("\n"); printf("*** INTERRUPTED ***\n");
	exit(1);
}

void print_stats() {
	printf("c CPU time			  : %g s\n", cpuTime()-initial_time);
	printf("d decisions %d\n", NDECIDE);
	printf("d conflicts %d\n", NCONFL);
	printf("d propagations %lld\n", NPROP);
	printf("d lp added constraints %d\n", NLPCONSTR);
	printf("d lp calls %d\n", NLPCALLS);
	printf("d lp optimalities %d\n", NLPOPTIMAL);
	printf("d lp trivial optimalities %d\n", NLPNOPIVOT);
	printf("d lp infeasibilities %d\n", NLPINFEAS);
	printf("d lp farkas constraints %d\n", NLPFARKAS);
	printf("d lp iterations %d\n", NLPPIVOTS);
	printf("d lp basis resets %d\n", NLPRESETBASIS);
	printf("d lp cycling count %d\n", NLPCYCLING);
	printf("d lp singular basis count %d\n", NLPSINGULAR);
	printf("d lp other abort count %d\n", NLPOTHER);
	printf("d lp has no primal %d\n", NLPNOPRIMAL);
	printf("d lp has no farkas %d\n", NLPNOFARKAS);
	printf("d lp phase differences %lld\n", NLPPHASEDIFF);
	printf("d lp dual cuts %lld\n", NLPDUALCUTS);
	printf("d lp learned cuts %lld\n", NLPLEARNEDCUTS);
	printf("d lp gomory cuts %d\n", NLPGOMORYCUTS);
	printf("d lp deleted cuts %lld\n", NLPDELETEDCUTS);
	printf("d lp solve time %.2f\n", LPSOLVETIME);
	printf("d lp total time %.2f\n", LPTIME);
	printf("d lp cut time %.2f\n", LPCUTTIME);
	printf("d lp average infeasibility depth %.2f\n", AVGLPINFEASDEPTH);
	printf("d average conflict depth %.2f\n", AVGCONFLDEPTH);
	printf("d lp internal gomory cuts %d\n", NLPGOMORYCUTSINTERNAL);
	printf("d lp internal infeasible gomory cuts %d\n", NLPGOMORYCUTSINTERNALINFEASIBLE);
	printf("d learned non-clausal %d\n", NGENEREALPB);
}

int last_sol_value;
vector<bool> last_sol;

bool checksol() {
	for(size_t i=(opt?1:0); i<clauses.size(); ++i){
		Clause& C = ca[clauses[i]];
		long long slack=-C.w;
		for(size_t j=0; j<C.size(); ++j){
			int l = C.lits()[j];
			slack+=((l>0)==last_sol[abs(l)])*C.coefs()[j];
		}
		if(slack<0) return false;
	}
	puts("c SATISFIABLE (checked)");
	return true;
}

void exit_SAT() {
	assert(checksol());
	print_stats();
	puts("s SATISFIABLE");
	printf("v");for(int i=1;i<=getNbOrigVars();i++)if(last_sol[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n");
	exit(10);
}

void exit_UNSAT() {
	if(!last_sol.empty()) exit_OPT();
	print_stats();
	puts("s UNSATISFIABLE");
	exit(20);
}

void exit_INDETERMINATE() {
	if (!last_sol.empty()) exit_SAT();
	print_stats();
	puts("s UNKNOWN");
	exit(0);
}

void exit_OPT() {
	assert(checksol());
	print_stats();
	cout << "s OPTIMUM FOUND" << endl;
	cout << "c objective function value " << last_sol_value << endl;
	printf("v");for(int i=1;i<=getNbOrigVars();i++)if(last_sol[i])printf(" x%d",i);else printf(" -x%d",i);printf("\n");
	exit(30);
}

void exit_ERROR(const std::initializer_list<std::string>& messages){
	cout << "Error: ";
	for(const string& m: messages) cout << m;
	std::cout << std::endl;
	exit(1);
}

void usage(int argc, char**argv) {
	printf("Usage: %s [OPTION] instance.(opb|cnf|wcnf)\n", argv[0]);
	printf("\n");
	printf("Options:\n");
	printf("  --help           Prints this help message\n");
	printf("  --verbosity=arg  Set the verbosity of the output (default %d).\n",verbosity);
	printf("\n");
	printf("  --var-decay=arg  Set the VSIDS decay factor (0.5<=arg<1; default %lf).\n",var_decay);
	printf("  --rinc=arg       Set the base of the Luby restart sequence (floating point number >=1; default %lf).\n",rinc);
	printf("  --rfirst=arg     Set the interval of the Luby restart sequence (integer >=1; default %d).\n",rfirst);
	printf("  --lp=arg         Set the ratio of #pivots/#conflicts to determine the linear solver's pivot allowance (negative means infinite, 0 means no LP solving) (float >=-1; default %lf).\n",lpmulti);
	printf("  --lp-phase=arg   Set whether the LP solutions influence the variable phase heuristic (0 or 1; default %d).\n",useLpPhase);
	printf("  --lp-sanitizefarkas=arg Set ratio of pruned coefficients to average coefficient in the Farkas constraint. (1e-9 to 1; default %lf).\n",sanitizeFarkas);
	printf("  --lp-learncuts=arg Set whether learned clauses are added as cuts to the LP (0 or 1; default %d).\n",learnCuts);
	printf("  --lp-adddualcuts=arg Set whether non-integral objective values should be cut (0 or 1; default %d).\n",addDualCuts);
	printf("  --lp-addgomorycuts=arg Set whether Gomory cuts should be generated from a feasible LP (0 or 1; default %d).\n",addGomoryCuts);
	printf("  --lp-deletecuts=arg Set whether non-tight cuts are deleted from the LP (0 or 1; default %d).\n",deleteCuts);
	printf("  --lp-tolerance=arg Set tolerance for floating point comparisons. Lower is less tolerant (0 to 1; default %e).\n",tolerance);
	printf("  --lp-maxcutcos=arg Set upper bound on cosine of angle between cuts added in one round. Higher means cuts can be more parallel (-1 to 1; default %e).\n",maxCutCos);
	printf("  --lp-cutroundlimit=arg Cap number of cuts added in one round. Lower means fewer cuts are added (0 to 1e6; default %d).\n",cutRoundLimit);
	printf("  --lp-useinternaloptimality=arg Set whether LP optimalities detected deep in the search node are exploited (0 or 1; default %d).\n",useInternalOptimality);
	printf("  --lp-decobjective=arg Set the coefficients for the LP solver's objective for decision instances (-1 or 0 or 1; default %d).\n",lpObjectiveCoef);
}

char * filename = 0;

typedef bool (*func)(double);
template <class T>
void getOption(const map<string, string>& opt_val, const string& option, func test, T& val){
	if (opt_val.count(option)) {
		double v = atof(opt_val.at(option).c_str());
		if (test(v)) val=v;
		else exit_ERROR({"Invalid value for ",option,": ",opt_val.at(option),".\nCheck usage with --help option."});
	}
}

void read_options(int argc, char**argv) {
	for(int i=1;i<argc;i++){
		if (!strcmp(argv[i], "--help")) {
			usage(argc, argv);
			exit(1);
		}
	}
	vector<string> opts = {
			"verbosity", "var-decay", "rinc", "rfirst",
			"lp", "lp-phase", "lp-sanitizefarkas",
			"lp-learncuts", "lp-adddualcuts", "lp-deletecuts", "lp-addgomorycuts",
			"lp-tolerance", "lp-maxcutcos", "lp-cutroundlimit",
			"lp-useinternaloptimality", "lp-decobjective"
	};
	map<string, string> opt_val;
	for(int i=1;i<argc;i++){
		if (string(argv[i]).substr(0,2) != "--") filename = argv[i];
		else {
			bool found = false;
			for(string& key : opts) {
				if (string(argv[i]).substr(0,key.size()+3)=="--"+key+"=") {
					found = true;
					opt_val[key] = string(argv[i]).substr(key.size()+3);
				}
			}
			if (!found) exit_ERROR({"Unknown option: ",argv[i],".\nCheck usage with --help option."});
		}
	}

	getOption(opt_val,"verbosity",[](double x)->bool{return true;},verbosity);
	getOption(opt_val,"var-decay",[](double x)->bool{return 0.5<=x && x<1;},var_decay);
	getOption(opt_val,"rinc",[](double x)->bool{return x>=1;},rinc);
	getOption(opt_val,"rfirst",[](double x)->bool{return x>=1;},rfirst);
	getOption(opt_val,"lp",[](double x)->bool{return x>=0;},lpmulti);
	getOption(opt_val,"lp-phase",[](double x)->bool{return x==1 || x==0;},useLpPhase);
	getOption(opt_val,"lp-sanitizefarkas",[](double x)->bool{return 1e-9<=x && x<=1;},sanitizeFarkas);
	getOption(opt_val,"lp-learncuts",[](double x)->bool{return x==1 || x==0;},learnCuts);
	getOption(opt_val,"lp-adddualcuts",[](double x)->bool{return x==1 || x==0;},addDualCuts);
	getOption(opt_val,"lp-addgomorycuts",[](double x)->bool{return x==1 || x==0;},addGomoryCuts);
	getOption(opt_val,"lp-deletecuts",[](double x)->bool{return x==1 || x==0;},deleteCuts);
	getOption(opt_val,"lp-tolerance",[](double x)->bool{return 0<=x && x<=1;},tolerance);
	getOption(opt_val,"lp-maxcutcos",[](double x)->bool{return -1<=x && x<=1;},maxCutCos);
	getOption(opt_val,"lp-cutroundlimit",[](double x)->bool{return -1<=x && x<=1e6;},cutRoundLimit);
	getOption(opt_val,"lp-useinternaloptimality",[](double x)->bool{return x==1 || x==0;},useInternalOptimality);
	getOption(opt_val,"lp-decobjective",[](double x)->bool{return x==1 || x==0 || x==-1;},lpObjectiveCoef);
}

int curr_restarts=0;
long long nconfl_to_restart=0;
//reduceDB:
int cnt_reduceDB=1;
bool recentConflict = false;
bool firstRun = true;

bool solve(vector<int> assumptions) {
	backjumpTo(0); // ensures assumptions are reset
	std::vector<unsigned int> assumptions_lim={0};
	assumptions_lim.reserve(assumptions.size());
	while (true) {
		CRef confl = propagate();
		if(confl==CRef_Undef && firstRun && LP_isActivated()){
			firstRun = false;
			double time = cpuTime();
			confl = LP_inProcess();
			LPTIME += (cpuTime()-time);
		}
		if(confl==CRef_Undef && recentConflict && LP_isActivated()){
			recentConflict = false;
			double time = cpuTime();
			confl = LP_tryRun();
			LPTIME += (cpuTime() - time);
		}
		if (confl == CRef_Unsat) {
			exit_UNSAT();
		}else if (confl != CRef_Undef) {
			have_confl:
			recentConflict = true;
			varDecayActivity();
			claDecayActivity();
			if (decisionLevel() == 0) {
				exit_UNSAT();
			}
			AVGCONFLDEPTH=(AVGCONFLDEPTH*NCONFL+decisionLevel())/(double) (NCONFL+1);
			NCONFL++; nconfl_to_restart--;
			if(NCONFL%1000==0){
				if (verbosity > 0) {
					printf("c #Conflicts: %10d | #Learnt: %10d | #Farkas: %10d | #Cuts: %10lld\n",NCONFL,(int)learnts.size(),NLPFARKAS,NLPGOMORYCUTS+NLPDUALCUTS+NLPLEARNEDCUTS);
					if(verbosity>2){
						// memory usage
						cout<<"c total clause space: "<<ca.cap*4/1024./1024.<<"MB"<<endl;
						cout<<"c total #watches: ";{int cnt=0;for(int l=-n;l<=n;l++)cnt+=(int)adj[l].size();cout<<cnt<<endl;}
						printf("c total #propagations: %lld / total #impl: %lld (eff. %.3lf)\n",NPROP,NIMPL,(double)NPROP/(double)NIMPL);
					}
				}
			}
			vector<int>lits;vector<int>coefs;int w;
			analyze(confl, lits, coefs, w);
			bool trivial = simplify_constraint(lits,coefs,w);
			_unused(trivial);
			assert(!trivial);
			// compute an assertion level
			// it may be possible to backjump further, but we don't do this
			int lvl = 0;
			for (int i=0; i<(int)lits.size(); i++)
				if (Level[-lits[i]] < decisionLevel())
					lvl = max(lvl, Level[-lits[i]]);
			assert(lvl < decisionLevel());
			backjumpTo(lvl);
			CRef cr = learnConstraint(lits,coefs,w);

			if (::slack(ca[cr]) == 0) {
				for (int i=0; i<(int)lits.size(); i++)
					if (Level[-lits[i]] == -1 && Level[lits[i]] == -1)
						uncheckedEnqueue(lits[i], cr);
			} else {
				// the learnt constraint is conflicting at the assertion level.
				// in this case, immediately enter a new conflict analysis again.
				confl = cr;
				goto have_confl;
			}
		} else {
			if(asynch_interrupt)exit_INDETERMINATE();
			if(nconfl_to_restart <= 0){
				backjumpTo(0);
				double rest_base = luby(rinc, curr_restarts++);
				nconfl_to_restart = (long long) rest_base * rfirst;
			}
			//if ((int)learnts.size()-(int)trail.size() >= max_learnts)
			if(NCONFL >= cnt_reduceDB * nbclausesbeforereduce) {
				if(LP_isActivated()){
					double time = cpuTime();
					CRef cr = LP_inProcess();
					LPTIME += (cpuTime()-time);
					if(cr==CRef_Unsat){
						exit_UNSAT();
					}else if(cr!=CRef_Undef){
						confl = cr;
						goto have_confl;
					}
				}
				reduceDB();
				cnt_reduceDB++;
				nbclausesbeforereduce += incReduceDB;
			}
			int next = 0;
			if(assumptions_lim.size()>(unsigned int) decisionLevel()+1)assumptions_lim.resize(decisionLevel()+1);
			while(assumptions_lim.back()<assumptions.size()){
				int l = assumptions[assumptions_lim.back()];
				if (~Level[-l]) return false;
				if (~Level[l]){
					++assumptions_lim.back();
				}else{
					next = l;
					assumptions_lim.push_back(assumptions_lim.back());
					break;
				}
			}
			if(next==0) next = pickBranchLit();
			if(next==0) return true;
			newDecisionLevel();
			NDECIDE++;
			uncheckedEnqueue(next,CRef_Undef);
		}
	}
}

int main(int argc, char**argv){
	read_options(argc, argv);
	initial_time = cpuTime();
	init();
	signal(SIGINT, SIGINT_exit);
	signal(SIGTERM,SIGINT_exit);
	signal(SIGXCPU,SIGINT_exit);
	if (filename != 0) {
		ifstream fin (filename);
		if (!fin)  exit_ERROR({"Could not open ",filename});
		file_read(fin);
	} else {
		if (verbosity > 0) std::cout << "c No filename given, reading from standard input." << std::endl;
		file_read(cin);
	}
	signal(SIGINT, SIGINT_interrupt);
	signal(SIGTERM,SIGINT_interrupt);
	signal(SIGXCPU,SIGINT_interrupt);

	std::cout << "c #variables=" << getNbOrigVars() << " #constraints=" << clauses.size()-(opt?1:0) << std::endl;

	if(LP_isActivated()){
		double time = cpuTime();
		LP_init();
		LPTIME+=(cpuTime()-time);
	}

	for (int m = opt_coef_sum; m >= 0; m--) {
		vector<int> aux;
		for (int i = 0; i < opt_K; i++) {
			if (m & (1 << i)) aux.push_back(  n-opt_K+1 + i);
			else              aux.push_back(-(n-opt_K+1 + i));
		}
		if (solve(aux)) {
			last_sol.resize(n+1-opt_K);
			for (int i=1;i<=n-opt_K;i++)if(~Level[i])last_sol[i]=true;else last_sol[i]=false;
			if (opt) {
				// m + sum(coeff[i]*~ell[i]) >= opt_coef_sum possible.
				// m + opt_coef_sum - sum(coeff[i]*ell[i]) >= opt_coef_sum possible.
				// sum(coeff[i]*ell[i]) <= m possible.
				// sum(coeff0[i]*x[i]) + opt_normalize_add <= m possible.
				// sum(coeff0[i]*x[i]) <= m - opt_normalize_add possible.
				int s = 0;
				Clause & C = ca[clauses[0]];
				for (int i=0; i<(int)C.size(); i++) if (abs(C.lits()[i]) <= n-opt_K) {
					if (~Level[C.lits()[i]]) s += C.coefs()[i];
				}
				assert(opt_coef_sum - s <= m);
				m = opt_coef_sum - s;
				last_sol_value = m - opt_normalize_add;
				cout << "o " << last_sol_value << endl;
				if(LP_isActivated()) getLP().changeLhsReal(0,1-last_sol_value);
			}
		} else break;
	}
	if (!opt) exit_SAT();
	else exit_OPT();
}
