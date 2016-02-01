// Qidioms #144. histogram
h:{@[(1+max x)#0;x;+;1]}

// reads in a text file returning an int matrix of characters' intensities
// x=file name
readFile:{
  // a ramp of printable characters arranged from darkest to lightest appearance
  ramp:`int$"@MBHENR#KWXDFPQASUZbdehx*8Gm&04LOVYkpq5Tagns69owz$CIu23Jcfry%1v7l+it[]{}?j|()=~!-/<>\"\\^_';,:`. ";
  // map of characters' visual values (indexed by character code)
  values:(1+max ramp)#0N;
  values[ramp]:til count ramp;
  // read the input file, mapping characters to their values
  values`int$read0 hsym`$x}

// converts image to binary by looking at average intensity
// and also makes lines equal length (required for transpose)
// x=int matrix
digitise:{
  // work out the line size
  sizefreq:h count each x;
  linesize:last iasc sizefreq;
  // find the dark/light threshold for the file
  minval:min min each x;
  maxval:max max each x;
  thresh:ceiling 0.5*minval+maxval;
  // convert lines to boolean (1b=dark/0b=light) lists
  lines:thresh>x;
  // replace nonstandard lines with blanks to preserve the separation of
  // back-to-back images
  @[lines;where not linesize=count each lines;{[x;y]x#0b}[linesize;]]}

// run lengths from bitmap: 0110001111b -> 1 2 3 4
runs:{{d:_[where differ x;x];count each d}each x}

// returns integer half x with truncation
half:{[x] `long$floor 0.5*x}

// search for finder patterns
// x=boolean matrix
patsearch:{[r]
  // alternating lengths of runs of same colour
  // indices of 1 1 3 1 1 runs (each being one row in finder pattern's kernel)
  c1:{-1+(`char$`int$37+12*ratios each x)ss\:"1I)1"} r;
  c:raze {[x;y] x,/:y}'[til[count c1];c1];
  // where each run begins
  o:0,/:sums each r;
  pb:c[;0],'o ./:c;
  //c[;1]+:5;
  pe:c[;0],'o ./:c+\:0 5;
  d:half pe-pb;

  //// if true then corresponding row (column) has at least one such pattern
  //h:not 0=count each c;
  //// which rows (columns) have kernel patterns
  //f:{(where differ (where x)-til sum x)_where x} h;
  //// a finder pattern's kernel must have at least three rows 
  //f:f where 2<count each f;
  //// indices of rows for the entire finder pattern (kernel plus frame around it)
  //i:{n:count x;o:`long$0.5*n;(first[x]-o)+til n+o+o} each f;
  ////-1"x:";show x;-1"r:";show r;-1"c:";show c;-1"h:";show h;
  //-1"f:";show f;
  ////-1"i:";show i;
  //brk
  (pb+d)!pe-pb}

// choose k from list of n
comb:{[k;l]
  n:count l;
  $[k<1;();
    k=1;enlist each l;
    k<n;raze {y[z],/:comb[x;(1+z)_y]}[k-1;l] each til 1+n-k;
    enlist l]}

//checkpts:{-1"x=";show x;-1"y=";show y;r:x where x[;y];-1"r=";show r;r}
//checkpts:{-1"x=";show x;-1"y=";show y;r:y,raze(where each x where x[;y])except\:y;-1"r=";show r;r}
// for a given set of segments' bitmaps and a pivot point, return all triples
// containing the pivot point and the ends of two segments originating from it
checkpts:{y,/:comb[2;]raze(where each x where x[;y])except\:y}

// z coordinate of cross product of two 2D vectors
crossprod:{(x[0;0]*x[1;1])-x[0;1]*x[1;0]}

// dot product
dot:{sum x*y}
dotprod:{dot[x 0;x 1]}
len:{sqrt dot[x;x]}
norm:{x%len x}

// swaps 2nd and 3rd vertices
swap12:{x 0 2 1}

// two vectors from triangle
trivec:{(x[1]-x 0;x[2]-x 0)}
// q))trivec each x@/:raze triples
// ((0 18;18 0);(0 18;18 0);(0 18;18 0);(0 18;18 0);(-27 0;27 0);(-27 0;27 0)..

// finds all isosceles right-angle triangles in a given set of vertices
// q)show x
// 4   21
// 22  3
// 22  21
// 31  21
// ..
// show grp x
// 4  3   4  21  22 3
// 30 3   30 21  48 3
// 57 3   57 21  75 3
// 84  3  84  21 102 3
grp:{
  // points' coordinates normalised by the size of the pattern module
  p:x*7%y;
  // distance between each pair of points
  m:`int${d:y-x;sqrt sum d*d}/:\:[p;p];
  // list of indices for each pair of points
  c:raze (til count m),/:\:til count m;
  // keep the lower triangle of c (m is symmetrical)
  c:c where {x[0]>x[1]} each c;
  // o is the order of coordinates for enumerating m in ascending order
  o:iasc m ./:c;
  // values of m in ascending order
  v:m ./:c o;
  //grouped:group m ./:c o;
  // pairs of indices (segments) grouped by distance between their points
  grouped:c (where differ v)_o;
  // we want three points or more, so discard groups with only one segment
  grouped:grouped where 1<count each grouped;
  // q))grouped
  // ((6 5;9 8);(1 0;2 0;4 3;5 3;7 6;8 6;10 9;11 9);(4 2;7 5;10 8)..
  // express each segment as a bitmap of indices of its points/vertices
  bitmaps:{{x[y]:11b;x}[x#0b;]each y}[count m;]each grouped;
  // q))bitmaps
  // ((000001100000b;000000001100b);(110000000000b;101000000000b;
  // work out which vertices appear multiple times in each group of segments
  pivots:{1<sum each flip x}each bitmaps;
  // q))pivots
  // (000000000000b;100100100100b;
  // whether we have any pivots in a given distance-group
  hp:any each pivots;
  // q))any each pivots
  // 010001100000000b
  f:{raze each[checkpts y;where x]};
  triples:raze f'[pivots where hp;bitmaps where hp];
  // q))show triples
  // (0 1 2;3 4 5;6 7 8;9 10 11)
  // (6 3 9;7 4 10;8 5 11)
  // (3 1 7;4 0 6;6 4 10;7 3 9)
  triangles:x@/:triples;
  // q))show triangles
  // 4  3   4  21  22 3
  // 30 3   30 21  48 3
  // convert triangles into pairs of vectors
  vecs:trivec each triangles;
  // see which pairs of vectors are oriented incorrectly
  rh:0>crossprod each vecs;
  // swap 2nd and 3rd vertices in those triples that need correcting
  triples[where rh]:swap12 each triples where rh;
  // return right-angled triangles only
  triples:triples where not dotprod each vecs;
  triples
  }

// takes a triangle (list of its coords) and the dims of finder patters
// at each vertex. returns a 3x3 matrix for transforming local vertex coords
// (zero-based, upright symbol) to image coords. also returns integer
// dimensions of the symbol (taken as coords, they would point beyond the
// bottom-right corner). the returned matrix takes vertices in homogeneous
// coordinates with z=1.
matandsize:{[x;y]
  // grp returns vertices in such order that
  // v 0 is down and v 1 is across the symbol
  v:trivec x;
  u:norm each v;
  // dimensions of finder patterns measured along symbol's axes (dimensions
  // might be negative for right-to-left or bottom-to-top orientations)
  s1:dot[u 0;]each y 0 1;
  s2:dot[u 1;]each y 0 2;
  // size of the symbol (either/both components could be negative)
  d1:half[s1 0]+dot[u 0;len v 0]+s1[1]-half s1 1;
  d2:half[s2 0]+dot[u 1;len v 1]+s2[1]-half s2 1;
  // avg size of the module: x1 is down/y and x2 is across/x the symbol
  x1:abs (sum s1)%14;
  //-1"x1=";show x1;
  x2:abs (sum s2)%14;
  //-1"x2=";show x2;
  // see if the symbol is oriented along the y axis
  ywise:abs[u . 0 0]>abs u . 0 1;
  vy:$[ywise;x1*u 0;x2*u 1];
  vx:$[ywise;x2*u 1;x1*u 0];
  // find the origin of the symbol
  p0:`float$((x . 0 0)-half[$[ywise;s1;s2] 0];(x . 0 1)-half[$[ywise;s2;s1] 0]);
  //-1"p0=";show p0;
  //-1"vy=";show vy;
  //-1"dot[vy;1 0]=",string dot[vy;1 0];
  //-1"vx=";show vx;
  //-1"dot[vx;0 1]=",string dot[vx;0 1];
  // use one-module origin offset if respective axis is inverted
  oy:$[ywise;x1;x2];
  ox:$[ywise;x2;x1];
  // transformation matrix from local symbol coordinates to image coords.
  m:(vy,p0[0]-(not 0<dot[vy;1 0])*oy;vx,p0[1]-(not 0<dot[vx;0 1])*ox;0. 0. 1.);
  //-1"x=";show x;
  //-1"m=";show m;
  pi:(0. 25. 0. 25.; 0. 0. 25. 25.;  4#1.);
  //-1"pi=";show pi;
  po:m mmu pi;
  //-1"po=";show po;
  (m;`int$abs(d1%x1;d2%x2))
  }

findsymbols:{
  r:runs x;
  // row-wise pattern search
  d:patsearch r;
  // column-wise pattern search (using transposed lines)
  e:patsearch runs 1+:/x;
  // swap coordinates of column-wise search bringing them to common basis
  e:(reverse each key e)!reverse each value e;
  // combine two dicts discarding entries that have a zero coord
  // (a zero means that pattern was not detected in the other direction)
  // p is a dict of coordinates of all detected finder patterns;
  // the value is the size of the pattern (centred around its coords)
  p:(where 0 in/:d+e)_d+e;
  // indices of vertices combined by three: first is the centre (pivot),
  // second is the bottom vertex, third is the right one.
  // the actual orientation of qr symbol may be different:
  // +-->  <--+     ^  ^      1: y=y,   x=x;
  // |        |     |  |      2: y=x,   x=w-y;
  // v        v  <--+  +-->   3: y=h-y, x=w-x;
  //  (1)   (2)   (3)   (4)   4: y=h-x, x=y.
  v:key p;
  s:value p;
  // group detected finder patterns into triples
  triples:grp[v;s];
  // look up coordinates of each triple
  triangles:v@/:triples;
  // also look up dimensions of finder patterns for each triple
  sizes:value[p]@/:triples;
  matandsize'[triangles;sizes]
  }

// extract a qr symbol from an image bitmap using the symbol's transformation
// matrix and size
extract:{[b;ms]
  m:ms 0;
  //-1"m=";show m;
  d:ms 1;
  cy:`float$raze flip(d 1)#enlist til d 0; // 000011112222..
  cx:`float$(prd d)#til d 1;               // 012301230123..
  cz:count[cx]#1.;
  c:m mmu (cy;cx;cz);
  //-1"coords=";show 26#flip`int$(c 0;c 1);
  // index b by pairs of coords from c and slice the result by symbol width
  retval:(d[1]*til d 0)_b ./:flip`int$(c 0;c 1);
  -1"retval=";show " @"retval;
  retval
  }

// returns a list of QR codes detected in a file
decode:{
  b:digitise readFile x;
  extract[b;]each findsymbols b;
  }

if[not null .z.f;
  args:.Q.opt .z.x;
  file:args`file;
  if[1>count file;file:enlist"solutions.txt"];
  show decode each file;
  exit 0;];
