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

//#include <assert.h>
//#include <map>
//#include <vector>
//#include <iostream>
//#include "core/SolverTypes.h"

//using namespace std;

static map<unsigned, vector<pair<unsigned,unsigned> > > DirOr2wiseMerge =
    (map<unsigned, vector<pair<unsigned,unsigned> > >) {
#include "DirOr2wiseMerge.cpp"
} ;

static map<unsigned, vector<pair<unsigned,unsigned> > > DirOr4wiseMerge = 
    (map<unsigned, vector<pair<unsigned,unsigned> > >) {
#include "DirOr4wiseMerge.cpp"
} ;

static int getOptFromDynamicMap(map<unsigned, vector<pair<unsigned,unsigned> > >& myMap, unsigned n, unsigned k) {
  map<unsigned, vector<pair<unsigned,unsigned> > >::iterator it = myMap.find(k);

  if( it == myMap.end() ) return 4;

  unsigned n0 = k;
  vector<pair<unsigned,unsigned> >::iterator vit = it->second.begin();

  while(vit != it->second.end()) {
    if( (n0 <= n) && (n < n0 + vit->second) )
      return vit->first;
    else
      n0+=vit->second;
    vit++;
  }

  it = myMap.find(1);
  vit = it->second.begin();
  unsigned sum = 0;
  while(vit != it->second.end()){  sum += vit->second; vit++; }
;
  if((n0-1) == sum) return (--vit)->first;

  return 4;
}


template <class Solver>
class Encoding_MW {
 private:
  void make2wiseMerge(vector<Lit> const& x, vector<Lit> const& y, vector<Lit>& outvars, unsigned int k);
  void make4wiseMerge(vector<Lit> const& a, vector<Lit> const& b, vector<Lit> const& c, vector<Lit> const& d, vector<Lit>& outvars, unsigned int k);

  void Direct4Combine(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k);
  void OddEvenCombine(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k);
  void make4OddEvenMerge(vector<Lit> const& a, vector<Lit> const& b, vector<Lit> const& c, vector<Lit> const& d, vector<Lit>& outvars, unsigned int k);
  void make2OddEvenMerge(vector<Lit> const& a, vector<Lit> const& b, vector<Lit>& outvars, unsigned int k);

  void make4Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit const& x4, Lit& y1, Lit& y2, Lit& y3, Lit& y4);
  void make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3);
  inline void make2Comparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2);

  bool makeDirectNetwork(const vector<Lit>& invars, vector<Lit>& outvars, unsigned k);
  void DirectCardClauses(const vector<Lit>& invars, unsigned start, unsigned pos, unsigned j, vec<Lit>& args);

  void DirectPairwiseMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k);
  void DirectMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k);
  void OddEvenPairwiseMerge(vector<Lit> const& in1, vector<Lit> const& in2,vector<Lit>& outvars, unsigned k);
  
  Solver* S;

  EncodingType ctype;
  
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
  
 public:
  bool make2wiseSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  bool make4wiseSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  bool make2OddEvenSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);
  bool make4OddEvenSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k);

  bool makeSelConstr(const vector<Lit>& invars, unsigned const k, vector<Lit>* outvars,
        bool (Encoding_MW<Solver>::*makeAtMostSel)(const vector<Lit>& in, vector<Lit>& out, unsigned const k));
  
  Encoding_MW(Solver* _S, EncodingType ct) : S(_S), ctype(ct) { }
  ~Encoding_MW() { }
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
    if (lastvar != lit_Undef) {
      vec<Lit> args;
      args.push(lastvar);
      args.push(~outvars[i]);
      S->addClause(args);
    }
    lastvar = outvars[i];
  }
  for (unsigned i = k ; i < outvars.size() ; i++) {
    if(outvars[i] == lit_Undef) continue;
    S->addClause(~outvars[i]);
  }
  
  return true;
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

  if (S->direct_net && (k<=1 || k==2 && n <= 39 || k==3 && n <= 10 || k==4 && n <= 8 || k<=7 && n<=7)) {
    makeDirectNetwork(invars, outvars, k);
    return true;
  }

  unsigned n1, n2;
  int p2 = (k==2 ? 1 : pow2roundup((k+4)/3));
  n2 = (n <= 7 ? n/2 : (abs((int)k/2-p2) > (k+3)/4 ? k/2 : (p2 <= k/2 ? p2 : k-p2)));
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
  if (S->direct_net && (getOptFromDynamicMap(DirOr2wiseMerge,n,k) == 1))
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
    int p2 = (k/2==2 ? 1 : pow2roundup((k/2+4)/3));
    n4 = (abs((int)k/4-p2) > (k/2+3)/4 || 4*p2 > n ? k/4 : p2);
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
  if (getOptFromDynamicMap(DirOr4wiseMerge,n,k) == 4) {
    make4wiseMerge(_a, _b, _c, _d, outvars, k);
  } else {
    vector<Lit> out1,out2;
    unsigned kout=min(k1+k2,k);
    DirectPairwiseMerge(_a,_b,out1,kout);
    DirectPairwiseMerge(_c,_d,out2,k/2);
    DirectPairwiseMerge(out1,out2,outvars,k);
  }
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
    Lit dout = lit_Error;
    S->newVar();
    dout = mkLit((unsigned int)S->nVars()-1);
    
    vec<Lit> args;
    args.push(~di[j]);
    args.push(dout);
    S->addClause(args);
    
    if (j+2 < n1) {
      args[0] = ~ai[j+2];
      S->addClause(args);
    }
    if (j+1 < n2) {
      args[0] = ~bi[j+1];
      S->addClause(args);
    }
    args[0] = ~ai[j+1];
    args[1] = ~ci[j];
    if (j > 0) args.push(~di[j-1]);
    args.push(dout);
    S->addClause(args);

    dnew[j] = dout;
  }
  for (unsigned j=0; j < (k+1)/4 && j+1 < n1; j++) {
    Lit cout = lit_Error;
    S->newVar();
    cout = mkLit((unsigned int)S->nVars()-1);

    vec<Lit> args;
    args.push(~ci[j]);
    args.push(cout);
    S->addClause(args);

    args[0] = ~ai[j+1];
    if (j > 0) {
      args[1] = ~di[j-1];
      args.push(cout);
    }
    S->addClause(args);

    cnew[j] = cout;
  }
  for (unsigned j=1; j < min(n2,k/4+1); j++) {
    Lit bout = lit_Error;
    S->newVar();
    bout = mkLit((unsigned int)S->nVars()-1);

    vec<Lit> args;
    args.push(~bi[j]);
    args.push(~di[j-1]);
    args.push(bout);
    S->addClause(args);
    if (j+1 < n1) {
      args[1] = ~ai[j+1];
      S->addClause(args);
    }
    bnew[j] = bout;
  }
  for (unsigned j=1; j < min(n1,k/4+1); j++) {
    Lit aout = lit_Error;
    S->newVar();
    aout = mkLit((unsigned int)S->nVars()-1);

    vec<Lit> args;
    args.push(~ai[j]);
    args.push(~ci[j-1]);
    args.push(~di[j-1]);
    if (j > 1) args.push(~di[j-2]);
    args.push(aout);
    S->addClause(args);
    
    if (j < n2) {
      args[2] = ~bi[j];
      S->addClause(args);
    }
    if (j+1 < n1) {
      args[2] = ~ai[j+1];
      S->addClause(args);
    }
    anew[j] = aout;
  }
  if (k >= 3 && k/4+1 < n1) {
    Lit aout = lit_Error;
    S->newVar();
    aout = mkLit((unsigned int)S->nVars()-1);

    vec<Lit> args;
    args.push(~ai[k/4+1]);
    if (k/4 > 0) args.push(~di[k/4-1]);
    if (k/4 < (k+1)/4) args.push(~ci[k/4]);
    args.push(aout);
    S->addClause(args);
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
bool Encoding_MW<Solver>::make2OddEvenSel(const vector<Lit>& invars, vector<Lit>& outvars, unsigned const k) {
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
 
  if (S->direct_net && (k <= 1 || k == 2 && n <= 9 || n <= 6)) {
    makeDirectNetwork(invars, outvars,k);
    return true;
  }
  
  // select sizes
  unsigned n1, n2;
  int p2 = (k==2 ? 1 : pow2roundup((k+4)/3));
  n2 = (n <= 7 ? n/2 : abs((int)k/2-p2) > (k+3)/4 ? (k <= n/2 ? k : k/2) : (2*p2 <= n/2 ? 2*p2 : p2) );
  n1 = n - n2;

  
  // split
  vector<Lit> x, y;
  for (unsigned i=0; i < n1; i++)
      x.push_back(invars[i]);
  for (unsigned i=n1; i < n; i++)
      y.push_back(invars[i]);

  // recursive calls
  vector<Lit> _x, _y;
  make2OddEvenSel(x, _x, min(k, n1));
  make2OddEvenSel(y, _y, min(k, n2));

  // merging
  make2OddEvenMerge(_x, _y, outvars, k);

  return true;
}

template<class Solver>
void Encoding_MW<Solver>::OddEvenCombine(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    if (k > a+b) k = a+b;   
 
    // set outvars[0] = in1[0];
    outvars.push_back(in1[0]);

    for (unsigned i = 0 ; i < (k-1)/2 ; i++) {
        outvars.push_back(lit_Error); outvars.push_back(lit_Error);
        make2Comparator(in2[i], in1[i+1], outvars[i*2+1], outvars[i*2+2]);
    }

    // set outvars[k-1] if needed
    if (k % 2 == 0)  // k is even
        if (k < a + b) {
      S->newVar();
      Lit ret = mkLit((unsigned)S->nVars()-1);
            outvars.push_back(ret);
      vec<Lit> args;
      // in2[k/2-1] -> ret
      args.push(~in2[k/2-1]);
      args.push(ret);
      S->addClause(args);
      // in1[k/2] -> ret
      args[0] = ~in1[k/2];
      S->addClause(args);
        }
        else if (a == b) outvars.push_back(in2[k/2-1]);
        else outvars.push_back(in1[k/2]);
}
    
template<class Solver>
void Encoding_MW<Solver>::make2OddEvenMerge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    
    if (a+b < k) k = a+b;
    if (a > k) a = k;
    if (b > k) b = k;
    if (a == 0) {
        for (unsigned i = 0 ; i < b ; i++) outvars.push_back(in2[i]);
  return;
    }
    if (b == 0) {
        for (unsigned i = 0 ; i < a ; i++) outvars.push_back(in1[i]);
  return;
    }
    if (a == 1 && b == 1) {
      if (k == 1) {
      S->newVar();
      Lit ret = mkLit((unsigned)S->nVars()-1);
            outvars.push_back(ret);
      vec<Lit> args;
      // in1[0] -> ret
      args.push(~in1[0]);
      args.push(ret);
      S->addClause(args);
      // in2[0] -> ret
      args[0] = ~in2[0];
      S->addClause(args);
      } else { // k == 2
        outvars.push_back(lit_Error); outvars.push_back(lit_Error);
        make2Comparator(in1[0], in2[0], outvars[0], outvars[1]);
      }
      return;
    }
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
    return true;
  }
  if (n==0) return true;
  if (n == 1) {
    outvars.push_back(invars[0]);
    return true;
  }
 
  if (S->direct_net && (k <= 1 || k == 2 && n <= 9 || n <= 6)) {
    makeDirectNetwork(invars, outvars,k);
    return true;
  }
  
  // select sizes
  unsigned n1, n2, n3, n4;
  if (n <= 7) { 
    n4=n/4; n3=(n+1)/4; n2=(n+2)/4; 
  } else {
    int p2 = (k/2==2 ? 1 : pow2roundup((k/2+4)/3));
    n4 = (abs((int)k/4-p2) > (k/2+3)/4 || 4*p2 > n ? k/4 : p2);
    n3 = (n == k && n4 == k/4 ? (k+1)/4 : n4);
    n2 = (n == k && n4 == k/4 ? (k+2)/4 : n4);
  }
  n1 = n - n2 - n3 - n4;
  
  // split
  vector<Lit> a, b, c, d;
  for (unsigned i=0; i < n1; i++) a.push_back(invars[i]);
  for (unsigned i=0; i < n2; i++) b.push_back(invars[n1+i]);
  for (unsigned i=0; i < n3; i++) c.push_back(invars[n1+n2+i]);
  for (unsigned i=0; i < n4; i++) d.push_back(invars[n1+n2+n3+i]);
  
  // recursive calls
  unsigned k1 = min(k, n1), k2 = min(k, n2), k3 = min(k, n3), k4 = min(k, n4);
  vector<Lit> _a, _b, _c, _d;
  make4OddEvenSel(a, _a, k1);
  make4OddEvenSel(b, _b, k2);
  make4OddEvenSel(c, _c, k3);
  make4OddEvenSel(d, _d, k4);

  // merging
  if (S->direct_net && (k >= 184 || getOptFromDynamicMap(DirOr4wiseMerge,n,k) == 4) ) {
      make4OddEvenMerge(_a, _b, _c, _d, outvars, k);
  } else {
      vector<Lit> out1,out2;
      DirectMerge(_a,_b,out1,min(k1+k2,k));
      DirectMerge(_c,_d,out2,min(k3+k4,k));
      DirectMerge(out1,out2,outvars,k);
  }
  return true;
}

template<class Solver>
void Encoding_MW<Solver>::Direct4Combine(vector<Lit> const& x, vector<Lit> const& y, vector<Lit>& outvars, unsigned k) {
    unsigned a = x.size(), b = y.size();
    assert(a >= b); assert(a <= b+4); assert(a >= 2); assert(b >= 1); 
    if (k > a+b) k = a+b;   

    // set outvars[0] = x[0];
    outvars.push_back(x[0]);
    unsigned last = (k < a+b || k % 2 == 1 || a == b+2 ? k : k-1);
    for (unsigned i = 0, j = 1 ; j < last ; j++,i=j/2) {
	S->newVar();
	Lit ret = mkLit((unsigned)S->nVars()-1);
        outvars.push_back(ret);
        if (j %2 == 0) {
	    if (i+1 < a && i < b+2) { 
	        // y[i-2] & x[i+1] -> ret
	        vec<Lit> args;
                args.push(~x[i+1]);
                if (i >= 2) args.push(~y[i-2]);
	        args.push(ret);
	        S->addClause(args);
            }
            if (i < a && i < b+1) {
	        // x[i] & y[i-1] -> ret
	        vec<Lit> args;
                args.push(~x[i]);
                args.push(~y[i-1]);
	        args.push(ret);
                S->addClause(args);
            }
        } else {
	    vec<Lit> args;
	    args.push(ret);
            if (i > 0 && i+2 < a) {
               // x[i+2] -> ret
               args.push(~x[i+2]);
               S->addClause(args);
               args.pop();
            } 
            if (i < b) {
               // y[i] -> ret
               args.push(~y[i]);
               S->addClause(args);
               args.pop();
            }
	    if (i+1 < a && i < b+1) {
                // x[i+1] & y[i-1] -> ret
                args.push(~x[i+1]);
                if (i > 0) args.push(~y[i-1]);
	        S->addClause(args);
            }
        }
    }
    if (k == a+b && k % 2 == 0 && a != b+2)
        if (a == b) outvars.push_back(y[b-1]);
        else outvars.push_back(x[a-1]);
}
    
template<class Solver>
void Encoding_MW<Solver>::make4OddEvenMerge(vector<Lit> const& a, vector<Lit> const& b, vector<Lit> const& c, vector<Lit> const& d, vector<Lit>& outvars, unsigned int k) {
    unsigned na = a.size(), nb = b.size(), nc = c.size(), nd = d.size();

    assert(na > 0); assert(na >= nb); assert(nb >= nc); assert(nc >= nd);
    if (na+nb+nc+nd < k) k = na+nb+nc+nd;
    if (na > k) na = k;
    if (nb > k) nb = k;
    if (nc > k) nc = k;
    if (nd > k) nd = k;
    
    if (nb == 0) {
        for (unsigned i = 0 ; i < na ; i++) outvars.push_back(a[i]);
	return;
    }
    if (na == 1) {       
      vector<Lit> invars;
      invars.push_back(a[0]);
      invars.push_back(b[0]);
      if (nc > 0) invars.push_back(c[0]);
      if (nd > 0) invars.push_back(d[0]);
      makeDirectNetwork(invars,outvars,k);
      return;
    }
    // from now on: na > 1 && nb > 0 
    vector<Lit> aodds, aevens, bodds, bevens, codds, cevens, dodds, devens, x, y;
    // split into odds and evens
    for (unsigned i = 0 ; i < na; i+=2) {
        aevens.push_back(a[i]);
        if (i + 1 < na) aodds.push_back(a[i+1]);
    }
    for (unsigned i = 0 ; i < nb; i+=2) {
        bevens.push_back(b[i]);
        if (i + 1 < nb) bodds.push_back(b[i+1]);
    }
    for (unsigned i = 0 ; i < nc; i+=2) {
        cevens.push_back(c[i]);
        if (i + 1 < nc) codds.push_back(c[i+1]);
    }
    for (unsigned i = 0 ; i < nd; i+=2) {
        devens.push_back(d[i]);
        if (i + 1 < nd) dodds.push_back(d[i+1]);
    }
    
    // recursive merges
    make4OddEvenMerge(aevens, bevens, cevens, devens, x, k/2+2);
    make4OddEvenMerge(aodds, bodds, codds, dodds, y, k/2);
    
    // combine results
    Direct4Combine(x,y,outvars,k);
}

template<class Solver>
void Encoding_MW<Solver>::make4Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit const& x4, Lit& y1, Lit& y2, Lit& y3, Lit& y4) {
  // if one of our inputs is a constant false, we use normal 3 comparator on the other three
  if (x1 == lit_Undef) {
    y4 = x1;
    make3Comparator(x2, x3, x4, y1, y2, y3);
    return;
  }
  if (x2 == lit_Undef) {
    y4 = x2;
    make3Comparator(x1, x3, x4, y1, y2, y3);
    return;
  }
  if (x3 == lit_Undef) {
    y4 = x3;
    make3Comparator(x1, x2, x4, y1, y2, y3);
    return;
  }
  if (x4 == lit_Undef) {
    y4 = x4;
    make3Comparator(x1, x2, x3, y1, y2, y3);
    return;
  }

  // otherwise we create new variables
  S->newVar();
  y1 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y2 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y3 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y4 = mkLit((unsigned int)S->nVars()-1);

  // 15-clause 4-comparator for AtMost constraint

  vec<Lit> args; // reused

  // x1 -> y1
  args.push(~x1);
  args.push(y1);
  S->addClause(args);
  
  // x2 -> y1
  args[0] = ~x2;
  // args[1] = y1;
  S->addClause(args);
  
  // x3 -> y1
  args[0] = ~x3;
  // args[1] = y1;
  S->addClause(args);

  // x4 -> y1
  args[0] = ~x4;
  // args[1] = y1;
  S->addClause(args);

  // x1 ^ x2 -> y2
  args[0] = ~x1;
  args[1] = ~x2;
  args.push(y2);
  S->addClause(args);
  
  // x1 ^ x3 -> y2
  // args[0] = ~x1;
  args[1] = ~x3;
  // args[2] = y2;
  S->addClause(args);

  // x1 ^ x4 -> y2
  // args[0] = ~x1;
  args[1] = ~x4;
  // args[2] = y2;
  S->addClause(args);
  
  // x2 ^ x3 -> y2
  args[0] = ~x2;
  args[1] = ~x3;
  // args[2] = y2;
  S->addClause(args);

  // x2 ^ x4 -> y2
  // args[0] = ~x2;
  args[1] = ~x4;
  // args[2] = y2;
  S->addClause(args);

  // x3 ^ x4 -> y2
  args[0] = ~x3;
  // args[1] = ~x4;
  // args[2] = y2;
  S->addClause(args);

  // x1 ^ x2 ^ x3 -> y3
  args[0] = ~x1;
  args[1] = ~x2;
  args[2] = ~x3;
  args.push(y3);
  S->addClause(args);

  // x1 ^ x2 ^ x4 -> y3
  // args[0] = ~x1;
  // args[1] = ~x2;
  args[2] = ~x4;
  // args[3] = y3;
  S->addClause(args);

  // x1 ^ x3 ^ x4 -> y3
  // args[0] = ~x1;
  args[1] = ~x3;
  // args[2] = ~x4;
  // args[3] = y3;
  S->addClause(args);

  // x2 ^ x3 ^ x4 -> y3
  args[0] = ~x2;
  // args[1] = ~x3;
  // args[2] = ~x4;
  // args[3] = y3;
  S->addClause(args);

  // x1 ^ x2 ^ x3 ^ x4 -> y4
  args[0] = ~x1;
  args[1] = ~x2;
  args[2] = ~x3;
  args[3] = ~x4;
  args.push(y4);
  S->addClause(args);
}

template<class Solver>
void Encoding_MW<Solver>::make3Comparator(Lit const& x1, Lit const& x2, Lit const& x3, Lit& y1, Lit& y2, Lit& y3) {
  // if one of our inputs is a constant false, we use normal comparator on the other two
  if (x1 == lit_Undef) {
    y3 = x1;
    make2Comparator(x2, x3, y1, y2);
    return;
  }
  if (x2 == lit_Undef) {
    y3 = x2;
    make2Comparator(x1, x3, y1, y2);
    return;
  }
  if (x3 == lit_Undef) {
    y3 = x3;
    make2Comparator(x1, x2, y1, y2);
    return;
  }

  // otherwise we create new variables
  S->newVar();
  y1 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y2 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  y3 = mkLit((unsigned int)S->nVars()-1);
  
  // 7-clause 3-comparator for AtMost constraint

  vec<Lit> args; // reused
  
  // x1 -> y1
  args.push(~x1);
  args.push(y1);
  S->addClause(args);
  
  // x2 -> y1
  args[0] = ~x2;
  // Already there: args[1] = y1;
  S->addClause(args);
  
  // x3 -> y1
  args[0] = ~x3;
  // Already there: args[1] = y1;
  S->addClause(args);
  
  // x1 ^ x2 -> y2
  args[0] = ~x1;
  args[1] = ~x2;
  args.push(y2);
  S->addClause(args);
  
  // x1 ^ x3 -> y2
  // Already there: args[0] = ~x1;
  args[1] = ~x3;
  // Already there: args[2] = y2;
  S->addClause(args);
  
  // x2 ^ x3 -> y2
  args[0] = ~x2;
  // Already there: args[1] = ~x3;
  // Already there: args[2] = y2;
  S->addClause(args);
  
  // x1 ^ x2 ^ x3 -> y3
  args[0] = ~x1;
  args[1] = ~x2;
  args[2] = ~x3;
  args.push(y3);
  S->addClause(args);
}

template<class Solver>
inline void Encoding_MW<Solver>::make2Comparator(Lit const& a, Lit const& b, Lit& c1, Lit& c2) {
  // if one of our inputs is a constant false, we can simplify greatly
  if (a == lit_Undef) {
    c1 = b;
    c2 = a;
    return;
  } else if (b == lit_Undef) {
    c1 = a; 
    c2 = b;
    return; 
  }
  // otherwise, we need new variables
  S->newVar();
  c1 = mkLit((unsigned int)S->nVars()-1);
  S->newVar();
  c2 = mkLit((unsigned int)S->nVars()-1);

  vec<Lit> args; // reused

  // 3-clause comparator,
  // because AtMosts only need implications from 0 on the outputs to 0 on the inputs

  // a -> c1
  args.push(~a);
  args.push(c1);
  S->addClause(args);
  
  // b -> c1
  args[0] = ~b;
  // Already there: args[1] = c1;
  S->addClause(args);

  // !c2 -> !a v !b'
  args[0] = ~a;
  args[1] = ~b;
  args.push(c2);
  S->addClause(args);
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

  if (b == 0) {
    for (unsigned i=0 ; i < c ; i++) outvars.push_back(in1[i]);
    return;
  }
  if (a == 0) {
    for (unsigned i=0 ; i < c ; i++) outvars.push_back(in2[i]);
    return;
  }

  for (unsigned i=0 ; i < c ; i++) {
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
  for (unsigned i=0 ; i < b ; i++) {
    vec<Lit> args;
    // in2[i] -> outvars[i]
    args.push(~in2[i]);
    args.push(outvars[i]);
    S->addClause(args);
  }
  for (unsigned j=0 ; j < b ; j++) {
    for(unsigned i=0 ; i < min(a,c-j-1) ; i++) {
      vec<Lit> args;
      // in1[i] ^ in2[j] -> outvars[i+j]
      args.push(~in1[i]);
      args.push(~in2[j]);
      args.push(outvars[i+j+1]);
      S->addClause(args);
    }
  }
}

template<class Solver>
void Encoding_MW<Solver>::OddEvenPairwiseMerge(vector<Lit> const& in1, vector<Lit> const& in2, vector<Lit>& outvars, unsigned k) {
    unsigned a = in1.size(), b = in2.size();
    
    if (a+b < k) k = a+b;
    if (a > k) a = k;
    if (b > k) b = k;
    if (a == 0) {
        for (unsigned i = 0 ; i < b ; i++) outvars.push_back(in2[i]);
	return;
    }
    if (b == 0) {
        for (unsigned i = 0 ; i < a ; i++) outvars.push_back(in1[i]);
	return;
    }
    if (a == 1 && b == 1) {
        outvars.push_back(in1[0]);
        if (k == 2) outvars.push_back(in2[0]);
        return;
    }
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

    // set outvars[0] = tmp1[0];
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
	    vec<Lit> args;
	    // tmp2[k/2-1] -> ret
	    args.push(~tmp2[k/2-1]);
	    args.push(ret);
	    S->addClause(args);
	    // tmp1[k/2] -> ret
	    args[0] = ~tmp1[k/2];
	    S->addClause(args);
        }
        else if (a % 2 == 0) outvars.push_back(tmp2[k/2-1]);
        else outvars.push_back(tmp1[k/2]);
}

#endif // __Encodings_MW_h
