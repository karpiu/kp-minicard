/****************************************************************************[Encodings_MW.h]
Copyright (c) 2016-2017, Michal Karpinski, Marek Piotrow

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef __Encodings_MW_h
#define __Encodings_MW_h

//using namespace std;


template <class Solver>
class Encoding_MW {
 public:
  bool makeSelConstr(const vector<Lit>& invars, unsigned const k, vector<Lit>* outvars,
        bool (Encoding_MW<Solver>::*makeAtMostSel)(const vector<Lit>& in, vector<Lit>& out, unsigned const k));
  
  bool make4OddEvenSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  bool make2OddEvenSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  bool make4wiseSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  bool make2wiseSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);

  Encoding_MW(Solver* _S, EncodingType ct) : S(_S), ctype(ct) { }
  ~Encoding_MW() { }
 
private:
  Solver* S;
  EncodingType ctype;
  
  void make4OddEvenMerge(vector<Lit> const in[4], vector<Lit>& outvars, unsigned int k);
  void make2OddEvenMerge(vector<Lit> const& a, vector<Lit> const& b, vector<Lit>& outvars, unsigned int k);

  void Direct4Combine(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k);
  void OddEvenCombine(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k);

  void make2wiseMerge(vector<Lit> const& x, vector<Lit> const& y, vector<Lit>& outvars, unsigned int k);
  void make4wiseMerge(vector<Lit> const& a, vector<Lit> const& b, vector<Lit> const& c, vector<Lit> const& d, vector<Lit>& outvars, unsigned int k);

  void make4Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit const& x4, Lit& y1, Lit& y2, Lit& y3, Lit& y4);
  void make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3);
  inline void make2Comparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2);

  bool makeDirectNetwork(const vector<Lit>& invars, vector<Lit>& outvars, unsigned k);
  void DirectCardClauses(const vector<Lit>& invars, unsigned start, unsigned pos, unsigned j, vec<Lit>& args);

  void DirectPairwiseMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k);
  void DirectMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k);
  void OddEvenPairwiseMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k);
  
  inline unsigned pow2roundup (unsigned x) {
    if(x == 0) return 0;
    --x;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return x+1;
  }
  inline void addClause(Lit const& x1, Lit const& x2) { 
    vec<Lit> args; args.push(x1); args.push(x2); S->addClause(args); }
  inline void addClause(Lit const& x1, Lit const& x2, Lit const& x3) { 
    vec<Lit> args; args.push(x1); args.push(x2); args.push(x3); S->addClause(args); }
  inline void addClause(Lit const& x1, Lit const& x2, Lit const& x3, Lit const& x4) { 
    vec<Lit> args; args.push(x1); args.push(x2); args.push(x3); args.push(x4); S->addClause(args); }
  inline void addClause(Lit const& x1, Lit const& x2, Lit const& x3, Lit const& x4, Lit const& x5) { 
    vec<Lit> args; args.push(x1); args.push(x2); args.push(x3); args.push(x4); args.push(x5); S->addClause(args); }
};

template<class Solver>
bool Encoding_MW<Solver>::makeSelConstr(const vector<Lit>& lits, unsigned const k, vector<Lit>* p_outvars,
    bool (Encoding_MW<Solver>::*makeAtMostSel)(const vector<Lit>& in, vector<Lit>& out, unsigned const k)) {
  // input vars
  vector<Lit> invars;
  for (unsigned i = 0 ; i < lits.size() ; i++) {
    invars.push_back(lits[i]);
  }

  //output vars
  vector<Lit> outvars;

  (this->*makeAtMostSel)(invars, outvars, k < lits.size() ? k+1 : k);
  
  for (unsigned i = 0 ; i < outvars.size() ; i++) {
    if (outvars[i] == lit_Undef)  continue;
    if (p_outvars) {
      p_outvars->push_back(outvars[i]);
    }
  }
  Lit lastvar = lit_Undef;
  for (unsigned i =  0; i < k ; i++) {
    if(outvars[i] == lit_Undef) continue;
    if (lastvar != lit_Undef) addClause(lastvar, ~outvars[i]);
    lastvar = outvars[i];
  }
  for (unsigned i = k ; i < outvars.size() ; i++) {
    if(outvars[i] == lit_Undef) continue;
    S->addClause(~outvars[i]);
  }
  
  return true;
}

static bool preferDirectMerge(unsigned n, unsigned k) {
    static unsigned minTest = 94, maxTest = 183;
    static unsigned short nBound[] = {
#include "DirOrRecursiveMerge.inl"
  } ;
  if (k > n) k = n;
  return k == 1 || k >= 4       && k <  minTest && n >= 10 ||
                   k >= minTest && k <= maxTest && n < nBound[k-minTest]; 
}

template<class Solver>
bool Encoding_MW<Solver>::make4OddEvenSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
  assert(outvars.empty());

  unsigned n = invars.size();

  assert(k <= n);

  if (k==0) {
    for (unsigned i = 0 ; i < n ; i++) {
      if(invars[i] == lit_Undef) continue;
      S->addClause(~invars[i]);
    }
  } else if (n == 1) outvars.push_back(invars[0]);
  else if (n > 1) {
    if (n <= 4 || S->direct_net && (k <= 1 || k == 2 && n <= 9 || n <= 6))
      makeDirectNetwork(invars, outvars,k);
    else {
      // select sizes
      unsigned nn[4], kk[4];
      unsigned p2 = pow2roundup((k+5)/6); // a power of 2 near k/4
      if (n >= 8 && 4*p2 <= n)  nn[1] = nn[2] = nn[3] = p2;
      else if (n < 8 || k == n) nn[1]=(n+2)/4, nn[2]=(n+1)/4, nn[3]=n/4;
      else                      nn[1] = nn[2] = nn[3] = k/4;
      nn[0] = n - nn[1] - nn[2] - nn[3];
  
      // split
      vector<Lit> in[4], out[4];
      for (int base=0, j=0; j < 4; base+=nn[j],j++)
        for (unsigned i=0; i < nn[j]; i++) in[j].push_back(invars[base+i]);
  
      // recursive calls
      for (int j=0; j < 4; j++)
        make4OddEvenSel(in[j], out[j], kk[j] = min(k,nn[j]));

      // merging
      if (S->direct_net && preferDirectMerge(kk[0]+kk[1]+kk[2]+kk[3], k) ) {
        vector<Lit> out1,out2;
        DirectMerge(out[0], out[1], out1, min(kk[0]+kk[1], k));
        DirectMerge(out[2], out[3], out2, min(kk[2]+kk[3], k));
        DirectMerge(out1, out2, outvars, k);
      } else
        make4OddEvenMerge(out, outvars, k);
    }
  }
  return true;
}

template<class Solver>
void Encoding_MW<Solver>::make4OddEvenMerge(vector<Lit> const in[4], vector<Lit>& outvars, unsigned int k) {
    long unsigned nn[4] = { in[0].size(), in[1].size(), in[2].size(), in[3].size() };

    assert(nn[0] > 0); assert(nn[0] >= nn[1]); assert(nn[1] >= nn[2]); assert(nn[2] >= nn[3]);
    k = min((long unsigned)k, nn[0] + nn[1] + nn[2] + nn[3]);
    for (int j=0; j < 4; j++) if (nn[j] > k) nn[j] = k;
    
    if (nn[1] == 0) {
        for (long unsigned i = 0 ; i < nn[0] ; i++) outvars.push_back(in[0][i]);
    } else if (nn[0] == 1) {       
      vector<Lit> invars;
      for (int j=0; j < 4; j++)
        if (nn[j] > 0) invars.push_back(in[j][0]);
      makeDirectNetwork(invars,outvars,k);
    } else {
      // from now on: nn[0] > 1 && nn[1] > 0 
      vector<Lit> even_odd[2][4], x, y;
      // split into odds and evens
      for (int j=0; j < 4; j++)
        for (long unsigned i = 0 ; i < nn[j]; i++)
          even_odd[i % 2][j].push_back(in[j][i]);
    
      // recursive merges
      make4OddEvenMerge(even_odd[0], x, k/2+2);
      make4OddEvenMerge(even_odd[1], y, k/2);
      // combine results
      if (nn[2] > 0) Direct4Combine(x,y,outvars,k); else OddEvenCombine(x,y,outvars,k);
    }
}

template<class Solver>
void Encoding_MW<Solver>::Direct4Combine(vector<Lit> const& x, vector<Lit> const& y, vector<Lit>& outvars, unsigned k) {
    unsigned a = x.size(), b = y.size();
    assert(a >= b); assert(a <= b+4); assert(a >= 2); assert(b >= 1); 
    if (k > a+b) k = a+b;

    // both x and y are sorted and the numbers of ones in them satisfy: ones(y) <= ones(x) <= ones(y)+4
    outvars.push_back(x[0]);
    unsigned last = (k < a+b || k % 2 == 1 || a == b+2 ? k : k-1);
    for (unsigned i = 0, j = 1 ; j < last ; j++,i=j/2) { // zip x with y and use two rows of comparators: first y[i] : x[i+2], then y[i] : x[i+1]
	S->newVar();
	Lit ret = mkLit((unsigned)S->nVars()-1);
        outvars.push_back(ret);
        if (j %2 == 0) { // new x[i] = min( max(y[i-1], x[i+1]), min(y[i-2], x[i]) ) = y[i-1] && x[i] || y[i-2] && x[i+1]
	    if (i+1 < a && i < b+2) // y[i-2] & x[i+1] -> ret
                if (i >= 2) addClause(~x[i+1], ~y[i-2], ret); else addClause(~x[i+1], ret);
            if (i < a && i < b+1) // x[i] & y[i-1] -> ret
                addClause(~x[i], ~y[i-1], ret);
        } else {  // new y[i] = max( max(y[i], x[i+2]), min(y[i-1], x[i+1]) ) = y[i] || x[i+2] || y[i-1] && x[i+1]
            if (i+2 < a) // x[i+2] -> ret
               addClause(~x[i+2], ret);
            if (i < b) // y[i] -> ret
               addClause(~y[i], ret);
	    if (i+1 < a && i < b+1) // x[i+1] & y[i-1] -> ret
                if (i > 0) addClause(~x[i+1], ~y[i-1], ret); else addClause(~x[i+1], ret);
        }
    }
    if (k == a+b && k % 2 == 0 && a != b+2)
        outvars.push_back(a == b ? y[b-1] : x[a-1]);
    if (k < a+b) {
      addClause(~x[a-1], ~y[b-1]);
      if (k+1 < a+b) {
        addClause(~x[a-2], ~y[b-1]); 
        if (b >= 2) addClause(~x[a-1], ~y[b-2]);
      }
    }
}
    
template<class Solver>
bool Encoding_MW<Solver>::make2OddEvenSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
  assert(outvars.empty());

  unsigned n = invars.size();

  assert(k <= n);

  if (k==0) {
    for (unsigned i = 0 ; i < n ; i++) {
      if(invars[i] == lit_Undef) continue;
      S->addClause(~invars[i]);
    }
  } else if (n == 1) {
    outvars.push_back(invars[0]);
  } else if (n > 1) {
    if (n <= 2 || S->direct_net && (k <= 1 || k == 2 && n <= 9 || n <= 6))
      makeDirectNetwork(invars, outvars,k);
    else {
      // select sizes
      unsigned n1, n2;
      int p2 = pow2roundup((k+2)/3);  // a power of 2 near k/2
      n2 = (n <= 7 ? n/2 : (2*p2 <= (int)n/2 ? 2*p2 : p2) );
      n1 = n - n2;
  
      // split
      vector<Lit> in1, in2, out1, out2;
      for (unsigned i=0; i < n1; i++) in1.push_back(invars[i]);
      for (unsigned i=n1; i < n; i++) in2.push_back(invars[i]);

      // recursive calls
      make2OddEvenSel(in1, out1, min(k, n1));
      make2OddEvenSel(in2, out2, min(k, n2));
      // merge
      if (S->direct_net && preferDirectMerge(out1.size()+out2.size(), k) )
        DirectMerge(out1, out2, outvars, k);
      else
        make2OddEvenMerge(out1, out2, outvars, k);
    }
  }
  return true;
}

template<class Solver>
void Encoding_MW<Solver>::make2OddEvenMerge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    
    if (a+b < k) k = a+b;
    if (a > k) a = k;
    if (b > k) b = k;
    if (a == 0) {
        for (unsigned i = 0 ; i < b ; i++) outvars.push_back(in2[i]);
    } else if (b == 0) {
        for (unsigned i = 0 ; i < a ; i++) outvars.push_back(in1[i]);
    } else if (a == 1 && b == 1) {
      if (k == 1) { // set the max output of a 2Comparator
        S->newVar();
        Lit ret = mkLit((unsigned)S->nVars()-1);
        outvars.push_back(ret);
        addClause(~in1[0], ret); // in1[0] -> ret
        addClause(~in2[0], ret); // in2[0] -> ret
      } else { // k == 2
        outvars.push_back(lit_Error); outvars.push_back(lit_Error);
        make2Comparator(in1[0], in2[0], outvars[0], outvars[1]);
      }
    } else {
    // from now on: a > 0 && b > 0 && && a,b <= k && 1 < k <= a + b 
    
    vector<Lit> in1odds, in2odds, in1evens, in2evens, tmp1, tmp2;
    // in1evens = in1[0,2,4,...], in2evens same
    // in1odds  = in1[1,3,5,...], in2odds same
    for (unsigned i = 0 ; i < a; i+=2) {
        in1evens.push_back(in1[i]);
        if (i + 1 < a) in1odds.push_back(in1[i+1]);
    }
    for (unsigned i = 0 ; i < b; i+=2) {
        in2evens.push_back(in2[i]);
        if (i + 1 < b) in2odds.push_back(in2[i+1]);
    }
    make2OddEvenMerge(in1evens, in2evens, tmp1, k/2+1);
    make2OddEvenMerge(in1odds, in2odds, tmp2, k/2);
    OddEvenCombine(tmp1,tmp2,outvars,k);
  }
}

template<class Solver>
void Encoding_MW<Solver>::OddEvenCombine(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    if (k > a+b) k = a+b;   
 
    outvars.push_back(in1[0]);
    for (unsigned i = 0 ; i < (k-1)/2 ; i++) {
        outvars.push_back(lit_Error); outvars.push_back(lit_Error);
        make2Comparator(in2[i], in1[i+1], outvars[i*2+1], outvars[i*2+2]);
    }

    // set outvars[k-1] if needed
    if (k % 2 == 0)
        if (k < a + b) { // set the max output of a 2Comparator
          S->newVar();
          Lit ret = mkLit((unsigned)S->nVars()-1);
          outvars.push_back(ret);
          addClause(~in2[k/2-1], ret); // in2[k/2-1] -> ret
          addClause(~in1[k/2], ret);   // in1[k/2] -> ret
        }
        else if (a == b) outvars.push_back(in2[k/2-1]);
        else outvars.push_back(in1[k/2]);
    if (k < a+b) addClause(~in1[a-1], ~in2[b-1]);
}
    
template<class Solver>
void Encoding_MW<Solver>::make2wiseMerge(vector<Lit> const& x, vector<Lit> const& y, vector<Lit>& outvars, unsigned int k) {
  unsigned n1 = x.size(), n2 = y.size();
  vector<Lit> xi = x, yi = y;
  unsigned h = pow2roundup(n1);

  for ( ; n2 < k/2 ; n2++) yi.push_back(lit_Undef);
  while (h > 1) {
    h = h/2;
    for (unsigned j=0; j<n2; j++) {
      Lit xout = lit_Error, yout = lit_Error;
      if(j+h < n1) {
        make2Comparator(xi[j+h], yi[j], yout, xout);
        xi[j+h] = xout; yi[j] = yout;
      }
    }
  }

  // copy k elements to outvars
  for (unsigned j=0; j<k; j++)
    outvars.push_back(j % 2 == 0 ? xi[j/2] : yi[j/2]);

  // set other literals to false
  for (unsigned j=(k+1)/2; j < n1; j++) 
     if (xi[j] != lit_Undef) S->addClause(~xi[j]);
}  

template<class Solver>
bool Encoding_MW<Solver>::make2wiseSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
  assert(outvars.empty());

  unsigned n = invars.size();

  assert(k <= n);

  if (k == 0) {
    for (unsigned i = 0 ; i < n ; i++) {
      if(invars[i] == lit_Undef) continue;
      S->addClause(~invars[i]);
    }
    return true;
  }

  if (n == 0) return true;
  if (n == 1) {
    outvars.push_back(invars[0]);
    return true;
  }

  if (n <= 2 || S->direct_net && (k <= 1 || k == 2 && n <= 9 || n <= 6)) {
    makeDirectNetwork(invars, outvars, k);
    return true;
  }

  unsigned n1, n2;
  int p2 = (pow2roundup((k+2)/3));
  n2 = (n <= 7 ? n/2 : p2 <= (int)k/2 ? p2 : k-p2);
  n1 = n - n2;

  // split
  vector<Lit> x, y;
  for (unsigned i=0; i < n2; i++) {
    x.push_back(lit_Error);
    y.push_back(lit_Error);
    make2Comparator(invars[2*i], invars[2*i+1], x[i], y[i]);
  }

  for (unsigned i=n2; i < n1; i++) {
    x.push_back(lit_Error);
    x[i] = invars[n2+i];
  }

  unsigned k1, k2;
  k1 = min(k, n1);
  k2 = min(k/2,n2);

  // recursive calls
  vector<Lit> _x, _y;
  make2wiseSel(x, _x, k1);
  make2wiseSel(y, _y, k2);

  // merging
  if (S->direct_net && preferDirectMerge(_x.size()+_y.size(),k))
    DirectPairwiseMerge(_x,_y,outvars,k);
  else
    make2wiseMerge(_x, _y, outvars, k);

  return true;
}

template<class Solver>
bool Encoding_MW<Solver>::make4wiseSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
  assert(outvars.empty());

  unsigned n = invars.size();

  assert(k <= n);

  if (k==0) {
    for (unsigned i = 0 ; i < n ; i++) {
      if(invars[i] == lit_Undef) continue;
      S->addClause(~invars[i]);
    }
    return true;
  }
  if (n==0) return true;
  if (n == 1) {
    outvars.push_back(invars[0]);
    return true;
  }
 
  if (k <= 1 || k == 2 && n <= 11 || n <= 6) {
    makeDirectNetwork(invars, outvars,k);
    return true;
  }
  
  unsigned n1, n2, n3, n4, j = 0;
  if (n <= 7) {
    n4 = n/4; n3 = (n+1)/4; n2 = (n+2)/4;
  } else {
    int p2 = (k <= 5 ? 1 : pow2roundup((k+8)/6));
    n4 = (4*p2 > (int)n ? k/4 : p2);
    n3 = (n == k && n4 == k/4 ? (k+1)/4 : n4);
    n2 = (n == k && n4 == k/4 ? (k+2)/4 : n4);
  }
  n1 = n - n2 - n3 - n4;
  
  // split
  vector<Lit> a, b, c, d;
  for (unsigned i=0; i < n4; i++,j+=4) {
    a.push_back(lit_Error);
    b.push_back(lit_Error);
    c.push_back(lit_Error);
    d.push_back(lit_Error);
    make4Comparator(invars[j], invars[j+1], invars[j+2], invars[j+3], a[i], b[i], c[i], d[i]);
  }
  for (unsigned i=n4; i < n3; i++,j+=3) {
    a.push_back(lit_Error);
    b.push_back(lit_Error);
    c.push_back(lit_Error);
    make3Comparator(invars[j], invars[j+1], invars[j+2], a[i], b[i], c[i]);
  }
  for (unsigned i=n3; i < n2; i++,j+=2) {
    a.push_back(lit_Error);
    b.push_back(lit_Error);
    make2Comparator(invars[j], invars[j+1], a[i], b[i]);
  }
  for (unsigned i=n2; i < n1; i++,j++) a.push_back(invars[j]);

  unsigned k1, k2, k3, k4;
  k1 = min(k, n1);
  k2 = min(k/2, n2);
  k3 = min(k/3, n3);
  k4 = min(k/4, n4);

  // recursive calls
  vector<Lit> _a, _b, _c, _d;
  make4wiseSel(a, _a, k1);
  make4wiseSel(b, _b, k2);
  make4wiseSel(c, _c, k3);
  make4wiseSel(d, _d, k4);

  // merging
  if (S->direct_net && preferDirectMerge(k1+k2+k3+k4,k)) {
    vector<Lit> out1,out2;
    unsigned kout=min(k1+k2,k);
    DirectPairwiseMerge(_a,_b,out1,kout);
    DirectPairwiseMerge(_c,_d,out2,k/2);
    DirectPairwiseMerge(out1,out2,outvars,k);
  } else
    make4wiseMerge(_a, _b, _c, _d, outvars, k);
  return true;
}

template<class Solver>
void Encoding_MW<Solver>::make4wiseMerge(vector<Lit> const& a, vector<Lit> const& b, vector<Lit> const& c, vector<Lit> const& d, vector<Lit>& outvars, unsigned int k) {
  unsigned n1 = a.size(), n2 = b.size(), n3 = c.size(), n4 = d.size();
  vector<Lit> ai = a, bi = b, ci = c, di = d;
  unsigned h = pow2roundup(n1);

  for ( ; n2 < min(n1-1,k/2) ; n2++) bi.push_back(lit_Undef);
  for ( ; n3 < min(n2-1,k/3) ; n3++) ci.push_back(lit_Undef);
  for ( ; n4 < k/4 ;           n4++) di.push_back(lit_Undef);
  while (h > 1) {
    h = h/2;

    for (unsigned j=0; j<n4; j++) {
      Lit aout = lit_Error, bout = lit_Error, cout = lit_Error, dout = lit_Error;
      if ((j+h < n3) && (j + 2*h < n2) && (j + 3*h < n1)) {
        make4Comparator(di[j], ci[j+h], bi[j+2*h], ai[j+3*h], dout, cout, bout, aout);
	di[j] = dout; ci[j+h] = cout; bi[j+2*h] = bout; ai[j+3*h] = aout;
      } else if ((j+h < n3) && (j + 2*h < n2)) {
        make3Comparator(di[j], ci[j+h], bi[j+2*h], dout, cout, bout);
	di[j] = dout; ci[j+h] = cout; bi[j+2*h] = bout;
      } else if (j+h < n3) {
        make2Comparator(di[j], ci[j+h], dout, cout);
	di[j] = dout; ci[j+h] = cout;
      }
    }

    for (unsigned j=0; j<min(n3,h); j++) {
      Lit aout = lit_Error, bout = lit_Error, cout = lit_Error;
      if ((j+h < n2) && (j + 2*h < n1)) {
        make3Comparator(ci[j], bi[j+h], ai[j+2*h], cout, bout, aout);
	ci[j] = cout; bi[j+h] = bout; ai[j+2*h] = aout;
      } else if (j+h < n2) {
        make2Comparator(ci[j], bi[j+h], cout, bout);
	ci[j] = cout; bi[j+h] = bout;
      }
    }

    for (unsigned j=0; j<min(n2,h); j++) {
      Lit aout = lit_Error, bout = lit_Error;
      if (j+h < n1) {
        make2Comparator(bi[j], ai[j+h], bout, aout);
        bi[j] = bout; ai[j+h] = aout;
      }
    }
  }

  // correction start
  vector<Lit> anew = ai, bnew = bi, cnew = ci, dnew = di;
  
  for (unsigned j=0; j < n4 && j+1 < n1; j++) {
    S->newVar();
    Lit dout = mkLit((unsigned int)S->nVars()-1);
    
    addClause(~di[j], dout);
    if (j+2 < n1) addClause(~ai[j+2], dout);
    if (j+1 < n2) addClause(~bi[j+1], dout);
    if (j > 0)    addClause(~ai[j+1], ~ci[j], ~di[j-1], dout); else addClause(~ai[j+1], ~ci[j], dout);
    dnew[j] = dout;
  }
  for (unsigned j=0; j < (k+1)/4 && j+1 < n1; j++) {
    S->newVar();
    Lit cout = mkLit((unsigned int)S->nVars()-1);

    addClause(~ci[j], cout);
    if (j > 0) addClause(~ai[j+1], ~di[j-1], cout); else addClause(~ai[j+1], cout);
    cnew[j] = cout;
  }
  for (unsigned j=1; j < min(n2,k/4+1); j++) {
    S->newVar();
    Lit bout = mkLit((unsigned int)S->nVars()-1);

    addClause(~bi[j], ~di[j-1], bout);
    if (j+1 < n1) addClause(~bi[j], ~ai[j+1], bout);
    bnew[j] = bout;
  }
  for (unsigned j=1; j < min(n1,k/4+1); j++) {
    S->newVar();
    Lit aout = mkLit((unsigned int)S->nVars()-1);

    if (j > 1) {
      addClause(~ai[j], ~ci[j-1], ~di[j-1], ~di[j-2], aout);
      if (j < n2) addClause(~ai[j], ~ci[j-1], ~bi[j], ~di[j-2], aout);
      if (j+1 < n1) addClause(~ai[j], ~ci[j-1], ~ai[j+1], ~di[j-2], aout);
    } else {
      addClause(~ai[j], ~ci[j-1], ~di[j-1], aout);
      if (j < n2) addClause(~ai[j], ~ci[j-1], ~bi[j], aout);
      if (j+1 < n1) addClause(~ai[j], ~ci[j-1], ~ai[j+1], aout);
    }
    anew[j] = aout;
  }
  if (k >= 3 && k/4+1 < n1) {
    S->newVar();
    Lit aout = mkLit((unsigned int)S->nVars()-1);

    if (k/4 > 0) {
      if (k/4 < (k+1)/4) addClause(~ai[k/4+1], ~di[k/4-1], ~ci[k/4], aout); else addClause(~ai[k/4+1], ~di[k/4-1],  aout);
    } else
      if (k/4 < (k+1)/4) addClause(~ai[k/4+1], ~ci[k/4], aout); else addClause(~ai[k/4+1],  aout);
    anew[k/4+1] = aout;    
  }
  // correction end

  // copy k elements to outvars
  for (unsigned j=0; j<k; j++)
    outvars.push_back(j % 4 == 0 ? anew[j/4] : (j % 4 == 1 ? bnew[j/4] : (j % 4 == 2 ? cnew[j/4] : dnew[j/4])));
  
  // set other literals to false
  for (unsigned j=(k+3)/4; j < n1; j++)
     if (ai[j] != lit_Undef) S->addClause(~anew[j]);
  for (unsigned j=(k+2)/4; j < n2; j++)
     if (bi[j] != lit_Undef) S->addClause(~bnew[j]);
  for (unsigned j=(k+1)/4; j < n3; j++)
     if (ci[j] != lit_Undef) S->addClause(~cnew[j]);
}

template<class Solver>
void Encoding_MW<Solver>::make4Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit const& x4, Lit& y1, Lit& y2, Lit& y3, Lit& y4) {
  // if one of our inputs is a constant false, use a 3-comparator on the other three
  if (x1 == lit_Undef)      y4 = x1, make3Comparator(x2, x3, x4, y1, y2, y3);
  else if (x2 == lit_Undef) y4 = x2, make3Comparator(x1, x3, x4, y1, y2, y3);
  else if (x3 == lit_Undef) y4 = x3, make3Comparator(x1, x2, x4, y1, y2, y3);
  else if (x4 == lit_Undef) y4 = x4, make3Comparator(x1, x2, x3, y1, y2, y3);
  else {
    // otherwise create new variables
    S->newVar(); y1 = mkLit((unsigned int)S->nVars()-1);
    S->newVar(); y2 = mkLit((unsigned int)S->nVars()-1);
    S->newVar(); y3 = mkLit((unsigned int)S->nVars()-1);
    S->newVar(); y4 = mkLit((unsigned int)S->nVars()-1);

    // 15-clause 4-comparator for AtMost constraint
    addClause(~x1, y1);                // x1 -> y1
    addClause(~x2, y1);                // x2 -> y1
    addClause(~x3, y1);                // x3 -> y1
    addClause(~x4, y1);                // x4 -> y1
    addClause(~x1, ~x2, y2);           // x1 ^ x2 -> y2
    addClause(~x1, ~x3, y2);           // x1 ^ x3 -> y2
    addClause(~x1, ~x4, y2);           // x1 ^ x4 -> y2
    addClause(~x2, ~x3, y2);           // x2 ^ x3 -> y2
    addClause(~x2, ~x4, y2);           // x2 ^ x4 -> y2
    addClause(~x3, ~x4, y2);           // x3 ^ x4 -> y2
    addClause(~x1, ~x2, ~x3, y3);      // x1 ^ x2 ^ x3 -> y3
    addClause(~x1, ~x2, ~x4, y3);      // x1 ^ x2 ^ x4 -> y3
    addClause(~x1, ~x3, ~x4, y3);      // x1 ^ x3 ^ x4 -> y3
    addClause(~x2, ~x3, ~x4, y3);      // x2 ^ x3 ^ x4 -> y3
    addClause(~x1, ~x2, ~x3, ~x4, y4); // x1 ^ x2 ^ x3 ^ x4 -> y4
  }
}

template<class Solver>
void Encoding_MW<Solver>::make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3) {
  // if one of our inputs is a constant false, use a comparator on the other two
  if (x1 == lit_Undef)      y3 = x1, make2Comparator(x2, x3, y1, y2);
  else if (x2 == lit_Undef) y3 = x2, make2Comparator(x1, x3, y1, y2);
  else if (x3 == lit_Undef) y3 = x3, make2Comparator(x1, x2, y1, y2);
  else {
    // otherwise create new variables
    S->newVar(); y1 = mkLit((unsigned int)S->nVars()-1);
    S->newVar(); y2 = mkLit((unsigned int)S->nVars()-1);
    S->newVar(); y3 = mkLit((unsigned int)S->nVars()-1);
  
    // 7-clause 3-comparator for AtMost constraint
    addClause(~x1, y1);                // x1 -> y1
    addClause(~x2, y1);                // x2 -> y1
    addClause(~x3, y1);                // x3 -> y1
    addClause(~x1, ~x2, y2);           // x1 ^ x2 -> y2
    addClause(~x1, ~x3, y2);           // x1 ^ x3 -> y2
    addClause(~x2, ~x3, y2);           // x2 ^ x3 -> y2
    addClause(~x1, ~x2, ~x3, y3);      // x1 ^ x2 ^ x3 -> y3
  }
}

template<class Solver>
inline void Encoding_MW<Solver>::make2Comparator(Lit const& x1, Lit const& x2, Lit& y1, Lit& y2) {
  // if one of the inputs is a constant false, we can simplify greatly
  if (x1 == lit_Undef)        y1 = x2, y2 = x1;
  else if (x2 == lit_Undef)   y1 = x1, y2 = x2;
  else {
    // otherwise, create new variables
    S->newVar(); y1 = mkLit((unsigned int)S->nVars()-1);
    S->newVar(); y2 = mkLit((unsigned int)S->nVars()-1);

    // 3-clause comparator for AtMost constraint
    addClause(~x1, y1);                // x1 -> y1
    addClause(~x2, y1);                // x2 -> y1
    addClause(~x1, ~x2, y2);           // x1 ^ x2 -> y2
  }
}

// Direct Sorting and Direct m-Cardinality Natwork
template<class Solver>
bool Encoding_MW<Solver>::makeDirectNetwork(const vector<Lit>& invars, vector<Lit>& outvars, unsigned k) {
  // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell:
  // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", page 11
  // k is the desired size of sorted output

  // outvars should be created in this function
  assert(outvars.empty());
  unsigned n = invars.size();
  
  if (k == 0 || k > n) k = n;

  for (unsigned i=0 ; i < k ; i++) {
    S->newVar();
    Lit ret = mkLit((unsigned)S->nVars()-1);
    outvars.push_back(ret);
  }
  for (unsigned j=1 ; j <= k ; j++) {
    vec<Lit> args;
    for (unsigned i=0 ; i < j; i++)
      args.push(lit_Error);
    args.push(outvars[j-1]);
    DirectCardClauses(invars, 0, 0, j, args);
  }
  return true;
}

//<<<<<<< HEAD
//=======
// Direct Merging and Simplified Direct Merging
/* template<class Solver> */
/* void Encoding_MW<Solver>::DirectMerge(vector<Lit> const& in1, vector<Lit> const& in2, */
/*                                       vector<Lit>& outvars, unsigned k) { */
/*     // as described in CP'2013 paper: Abio, Nieuwenhuis, Oliveras and Rodriguez-Carbonell: */
/*     // "A Parametric Approach for Smaller and Better Encodings of Cardinality Constraints", page 11 */

/*     unsigned a = in1.size(), b = in2.size(); */
/*     if (k > a + b) k = a + b; */
/*     if (a > k) a = k; */
/*     if (b > k) b = k; */
    
/*     for (unsigned i=0 ; i < k ; i++) { */
/*         S->newVar(); */
/*         Lit ret = mkLit((unsigned)S->nVars()-1); */
/*         outvars.push_back(ret); */
/*     } */
/*     for (unsigned i=0 ; i < a ; i++) { */
/*         vec<Lit> args; */
/*         // in1[i] -> outvars[i] */
/*         args.push(~in1[i]); */
/*         args.push(outvars[i]); */
/*         S->addClause(args); */
/*         args.push(lit_Error); */
/*         for (unsigned j=0 ; j < b && i + j + 1 < k ; j++) { */
/*             // in1[i] & in2[j] -> outvars[i+j+1] */
/*             args[1] = ~in2[j]; */
/*             args[2] = outvars[i+j+1]; */
/*             S->addClause(args); */
/*         } */
/*     } */
/*     for (unsigned j=0 ; j < b ; j++) { */
/*         vec<Lit> args; */
/*         // in2[i] -> outvars[i] */
/*         args.push(~in2[j]); */
/*         args.push(outvars[j]); */
/*         S->addClause(args); */
/*     } */
/* } */


/* >>>>>>> e5eca5c77ade8878e1c224d56c1ef204d81110eb */
template<class Solver>
void Encoding_MW<Solver>::DirectCardClauses(const vector<Lit>& invars, unsigned start, unsigned pos, unsigned j, vec<Lit>& args) {
  unsigned n = invars.size();
  if (pos == j) {
    S->addClause(args);
  } else {
    for (unsigned i = start ; i <= n - (j - pos) ; i++) {
      args[pos] = ~invars[i];
      DirectCardClauses(invars, i+1, pos+1, j, args);
    }
  }  
}

template<class Solver>
void Encoding_MW<Solver>::DirectPairwiseMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k) {
  unsigned a = in1.size(), b = in2.size(), c = k;
  if (c > a + b) c = a + b;
  if (a > c) a = c;
  if (b > c) b = c;

  //<<<<<<< HEAD
  if (b == 0) {
    for (unsigned i=0 ; i < c ; i++) outvars.push_back(in1[i]);
    return;
  }

  //=======
  //>>>>>>> e5eca5c77ade8878e1c224d56c1ef204d81110eb
  for (unsigned i=0 ; i < k ; i++) {
    S->newVar();
    Lit ret = mkLit((unsigned)S->nVars()-1);
    outvars.push_back(ret);
  }

  for (unsigned i=0 ; i < a ; i++) {
    vec<Lit> args;
    // in1[i] -> outvars[i]
    args.push(~in1[i]);
    args.push(outvars[i]);
    S->addClause(args);
  }
  for (unsigned i=0 ; i < min(b,c/2) ; i++) {
    vec<Lit> args;
    // in2[i] -> outvars[2*i]
    args.push(~in2[i]);
    args.push(outvars[2*i+1]);
    S->addClause(args);
  }
  for (unsigned j=0 ; j < b ; j++) {
    for(unsigned i=j+1 ; i < min(a,c-j-1) ; i++) {
      vec<Lit> args;
      // in1[i] ^ in2[j] -> outvars[i+j]
      args.push(~in1[i]);
      args.push(~in2[j]);
      args.push(outvars[i+j+1]);
      S->addClause(args);
    }
  }
}

//<<<<<<< HEAD
template<class Solver>
void Encoding_MW<Solver>::DirectMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k) {
  unsigned a = in1.size(), b = in2.size(), c = k;
  if (c > a + b) c = a + b;
  if (a > c) a = c;
  if (b > c) b = c;

  if (b == 0)      for (unsigned i=0 ; i < c ; i++) outvars.push_back(in1[i]);
  else if (a == 0) for (unsigned i=0 ; i < c ; i++) outvars.push_back(in2[i]);
  else {
    for (unsigned i=0 ; i < c ; i++) {
      S->newVar();
      Lit ret = mkLit((unsigned)S->nVars()-1);
      outvars.push_back(ret);
    }

    for (unsigned i=0 ; i < a ; i++) addClause(~in1[i], outvars[i]); // in1[i] -> outvars[i]
    for (unsigned i=0 ; i < b ; i++) addClause(~in2[i], outvars[i]); // in2[i] -> outvars[i]
    for (unsigned j=0 ; j < b ; j++)
      for(unsigned i=0 ; i < min(a,c-j-1) ; i++) addClause(~in1[i], ~in2[j], outvars[i+j+1]); // in1[i] ^ in2[j] -> outvars[i+ji+1]
  }
}

template<class Solver>
void Encoding_MW<Solver>::OddEvenPairwiseMerge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    
    if (a+b < k) k = a+b;
    if (a > k) a = k;
    if (b > k) b = k;
    if (a == 0)       for (unsigned i = 0 ; i < b ; i++) outvars.push_back(in2[i]);
    else if (b == 0)  for (unsigned i = 0 ; i < a ; i++) outvars.push_back(in1[i]);
    else if (a == 1 && b == 1) {
        outvars.push_back(in1[0]);
        if (k == 2) outvars.push_back(in2[0]);
        return;
    } else {
      // from now on: a > 0 && b > 0 && && a,b <= k && 1 < k <= a + b 
    
      vector<Lit> in1odds, in2odds, in1evens, in2evens, tmp1, tmp2;
      // in1evens = in1[0,2,4,...], in2evens same
      // in1odds  = in1[1,3,5,...], in2odds same
      for (unsigned i = 0 ; i < a; i+=2) {
        in1evens.push_back(in1[i]);
        if (i + 1 < a) in1odds.push_back(in1[i+1]);
      }
      for (unsigned i = 0 ; i < b; i+=2) {
        in2evens.push_back(in2[i]);
        if (i + 1 < b) in2odds.push_back(in2[i+1]);
      }
      OddEvenPairwiseMerge(in1evens, in2evens, tmp1, k/2+1);
      OddEvenPairwiseMerge(in1odds, in2odds, tmp2, k/2);

      outvars.push_back(tmp1[0]);

      for (unsigned i = 0 ; i < (k-1)/2 ; i++) {
        outvars.push_back(lit_Error); outvars.push_back(lit_Error);
        make2Comparator(tmp2[i], tmp1[i+1], outvars[i*2+1], outvars[i*2+2]);
      }

      // set outvars[k-1] if needed
      if (k % 2 == 0)  // k is even
        if (k < a + b) {
	    S->newVar();
	    Lit ret = mkLit((unsigned)S->nVars()-1);
            outvars.push_back(ret);
	    addClause(~tmp2[k/2-1], ret); // tmp2[k/2-1] -> ret
	    addClause(~tmp1[k/2], ret);   // tmp1[k/2] -> ret
        }
        else if (a % 2 == 0) outvars.push_back(tmp2[k/2-1]);
        else outvars.push_back(tmp1[k/2]);
  }
}

#endif // __Encodings_MW_h
