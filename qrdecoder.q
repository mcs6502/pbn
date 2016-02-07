// Qidioms #144. histogram
h:{@[(1+max x)#0;x;+;1]}

// reads debug image in raw format
readdata:{b:read1 hsym`$x;`int$(0N;floor sqrt count b)#b}

// reads in a text file returning an int matrix of characters' intensities
// x=file name
readFile:{
  // a ramp of printable characters arranged from darkest to lightest appearance
  ramp:`int$"@MBHENR#KWXDFPQASUZbdehx*8Gm&04LOVYkpq5Tagns69owz$CIu23Jcfry%1v7l+it[]{}?j|()=~!-/<>\"\\^_';,:`. ";
  // map of characters' visual values (indexed by character code)
  values:(1+max ramp)#0N;
  values[ramp]:til count ramp;
  // read the input file, mapping characters to their values
  $[x like "*.dat";
    readdata x;
    values`int$read0 hsym`$x]
  }

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
  if[not retval . 3 3;retval:not retval];
  //-1"retval=";show " @"retval;
  retval
  }

// decodes format information from the qr symbol
getfmt:{[qr]
  validfmts:(101010000010010b;101000100100101b;101111001111100b;101101101001011b;100010111111001b;100000011001110b;100111110010111b;100101010100000b;111011111000100b;111001011110011b;111110110101010b;111100010011101b;110011000101111b;110001100011000b;110110001000001b;110100101110110b;001011010001001b;001001110111110b;001110011100111b;001100111010000b;000011101100010b;000001001010101b;000110100001100b;000100000111011b;011010101011111b;011000001101000b;011111100110001b;011101000000110b;010010010110100b;010000110000011b;010111011011010b;010101111101101b);
  c1:flip (reverse(til 6),(7+til 2),(count[qr]-7)+til 7;15#8);
  //-1"c1=";show c1;
  c2:flip (15#8;(til 6),(7+til 1),(count[qr 8]-8)+til 8);
  //-1"c2=";show c2;
  c3:flip (15#8;(til 6),(7+til 2),(count[qr 8]-7)+til 7);
  c4:(7#c1),-8#c2;
  c5:(8#c3),-7#c1;
  fmts:qr ./:/:(c1;c2;c3;c4;c5);
  // see which of the valid formats has the least error compared to the
  // five formats obtained from the symbol
  errs:min each(sum each)each not fmts=\:/:validfmts;
  err:min errs;
  //-1"err=",string err;
  first where $[err<3;errs;()]=err
  }

mask0:{[x] not(x[0]+x 1)mod 2}
mask1:{[x] not x[0] mod 2}
mask2:{[x] not x[1] mod 3}
mask3:{[x] not(x[0]+x 1)mod 3}
mask4:{[x] not((x[0] div 2)+x[1] div 3)mod 2}
mask5:{[x] a:x[0]*x 1;not(a mod 2)+a mod 3}
mask6:{[x] a:x[0]*x 1;not((a mod 2)+a mod 3)mod 2}
mask7:{[x] a:x[0]*x 1;b:x[0]+x 1;not((b mod 2)+a mod 3)mod 2}
masks:(mask0;mask1;mask2;mask3;mask4;mask5;mask6;mask7);
//showmask:{-1 each" @"0N 14#value x;-1"";}
//showmask each masks,\:enlist (flip 14 14#til 14;14 14#til 14)

// generates the snake path across the entire symbol
// returning an array of coordinates
snake:{[h;w]
  // the path does not include column #6 because it is reserved in entirety
  i:til h*w-1;
  // o is the offset for skipping over column #6
  o:i>=h*w-7;
  // j is the index of 2-column ribbon piece
  j:i div 2*h;
  // d is the direction: 0=up, 1=down
  d:j mod 2;
  r:(i div 2)mod h;
  c:(i mod 2)+2*j;
  flip((d*r)+(1-d)*h-1+r;w-1+c+o)}

alignpos:(
  `long$();
  `long$();
  6 18;
  6 22;
  6 26;
  6 30;
  6 34;
  6 22 38;
  6 24 42;
  6 26 46;
  6 28 50;
  6 30 54;
  6 32 58;
  6 34 62;
  6 26 46 66;
  6 26 48 70;
  6 26 50 74;
  6 30 54 78;
  6 30 56 82;
  6 30 58 86;
  6 34 62 90;
  6 28 50 72 94;
  6 26 50 74 98;
  6 30 54 78 102;
  6 28 54 80 106;
  6 32 58 84 110;
  6 30 58 86 114;
  6 34 62 90 118;
  6 26 50 74 98 122;
  6 30 54 78 102 126;
  6 26 52 78 104 130;
  6 30 56 82 108 134;
  6 34 60 86 112 138;
  6 30 58 86 114 142;
  6 34 62 90 118 146;
  6 30 54 78 102 126 150;
  6 24 50 76 102 128 154;
  6 28 54 80 106 132 158;
  6 32 58 84 110 136 162;
  6 26 54 82 110 138 166;
  6 30 58 86 114 142 170);

// returns true if coords belong to reserved region in the symbol
reserved:{[v;c]
  y:c .(::;0);
  x:c .(::;1);
  s:8+4*v;
  //-1"s=",string[s];
  // root finder pattern--present in all versions
  ((y<9)&x<9)|
  // timing patterns in version 0
  ((not v)&(not y)|not x)|
  // the other two finder patterns and timing patterns in version 1 and greater
  ((0<v)&(y=6)|(x=6)|((y<9)&x>s)|(y>s)&x<9)|
  // alignment patterns (their number and location are version-dependent)
  // check that both coords are within 2 modules of alignment pattern's centre,
  // and that they do not fall in either of the non-central finder patterns
  ((any 3>abs y-/:alignpos v)&(any 3>abs x-/:alignpos v)&not ((y<9)&x>=s)|(y>=s)&x<9)|
  // two version information areas in version 7 and higher
  ((6<v)&((y<6)&(x<=s)&x>s-3)|((y<=s)&(y>s-3)&x<6))
  }

eccinfo:([ver:`int$();ecl:`symbol$()] ncw:`int$();necc:`int$();p:`int$();b:();c:();k:();r:());
insert[`eccinfo;(2;`L;44;10;2;enlist 1;enlist 44;enlist 34;enlist 4)];
insert[`eccinfo;(2;`M;44;16;0;enlist 1;enlist 44;enlist 28;enlist 8)];
insert[`eccinfo;(2;`Q;44;22;0;enlist 1;enlist 44;enlist 22;enlist 11)];
insert[`eccinfo;(2;`H;44;28;0;enlist 1;enlist 44;enlist 16;enlist 14)];
insert[`eccinfo;(5;`L;134;26;0;enlist 1;enlist 134;enlist 108;enlist 13)];
insert[`eccinfo;(5;`M;134;48;0;enlist 2;enlist 67;enlist 43;enlist 12)];
insert[`eccinfo;(5;`Q;134;72;0;2 2;33 34;15 16;9 9)];
insert[`eccinfo;(5;`H;134;88;0;2 2;33 34;11 12;11 11)];
insert[`eccinfo;(8;`L;242;48;0;enlist 2;enlist 121;enlist 97;enlist 12)];
insert[`eccinfo;(8;`M;242;88;0;2 2;60 61;38 39;11 11)];
insert[`eccinfo;(8;`Q;242;132;0;4 2;40 41;18 19;11 11)];
insert[`eccinfo;(8;`H;242;156;0;4 2;40 41;14 15;13 13)];

// de-interleaves codewords: bc=block counts; bs=block sizes
unravel:{[bc;bs;cw]
  //-1"bc=";show bc;
  //-1"bs=";show bs;
  //-1"count cw=",string count cw;
  n:sum bc;
  //-1"n=",string n;
  i:n*bs 0;
  //-1"i=",string i;
  blocks:flip (0N;n)#i#cw;
  //-1"n1=",string count blocks;
  $[i<count cw;
    [ends:flip (0N;bc[1])#i _ cw;
    //-1"n2=",string count ends;
    (bc[0]#blocks),((neg bc[1])#blocks),'ends];
    blocks]
  }

applyecc:{[db;cb] db}

modes:7 1 2 4 8 3 5 9 0!`ECI`Num`Alpha`Byte`Kanji`Append`FNC1a`FNC1b`Term;

sizes:{[v;m]
  (`Num`Alpha`Byte`Kanji!
    $[(0<v)&10>v;
      10 9 8 8;
      (9<v)&27>v;
      12 11 16 10;
      (26<v)&41>v;
      14 13 16 12;
      0N 0N 0N 0N])[m]
  }

decode:{[qr]
  //-1"qr=";show qr;
  fmt:getfmt qr;
  ec:`M`L`H`Q fmt div 8;
  maskno:fmt mod 8;
  //-1"ec=",string[ec];
  //-1"maskno=",string maskno;
  w:count qr 0;
  h:count qr;
  //-1"h=",string[h],", w=",string[w];
  allcoords:(flip(w;h)#til h;(h;w)#til w);
  //-1"allcoords=";show allcoords;
  mask:value masks[maskno],enlist allcoords;
  //-1"mask=";show" @"mask;
  // release the data masking
  qr:not qr=mask;
  //-1"qr=";show" @"qr;
  c:snake[h;w];
  //-1"#c=",string count c;
  //-1"c=";show c;
  v:(w-17)div 4;
  //-1"v=",string v;
  //-1"n=",string sum not reserved[v;c];
  //show reserved[v;flip allcoords];
  cwbits:qr ./:c where not reserved[v;c];
  //-1"#cwbits=",string count cwbits;
  // slice into codewords discarding remainder bits
  cw:0N 8#(neg count[cwbits]mod 8)_cwbits;
  // # of data and ecc blocks depends on the symbol version and ecc level
  bi:exec from eccinfo where ver=v,ecl=ec;
  // split codewords into data and code sequences
  cwseq:(`int$0;bi[`ncw]-bi`necc)_cw;
  //-1"count each cwseq="," "sv string count each cwseq;
  //-1"cwseq 0=";show cwseq 0;
  db:unravel[bi`b;bi`k;cwseq 0];
  //-1"db=";show db;
  cb:unravel[bi`b;bi[`c]-bi`k;cwseq 1];
  // obtain bit stream by combining data blocks
  bits:raze raze each applyecc'[db;cb];
  // the mode field is 4 bits for qr symbols (add support for micro qr later)
  modebits:4;
  //show 2 sv modebits#bits;
  m:modes 2 sv modebits#bits;
  //-1"m=",string m;
  sizebits:sizes[v;m];
  //-1"sizebits=",string sizebits;
  size:2 sv sizebits#modebits _ bits;
  //-1"size=",string size;
  db:8*size;
  bytes:"x"$2 sv/:(0N;8)#db#(modebits+sizebits)_bits;
  //-1"bytes=";show bytes;
  data:"c"$bytes;
  //-1"data=";show data;
  data
  }

// returns a list of QR codes detected in the input file
process:{[x]
  b:digitise readFile x;
  //show b;
  decode each extract[b;] each findsymbols b
  //brk;
  }

if[not null .z.f;
  args:.Q.opt .z.x;
  file:args`file;
  if[1>count file;file:enlist"solutions.txt"];
  (show each) each process each file;
  exit 0;];
