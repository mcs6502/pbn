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

// search for finder patterns
// x=boolean matrix
patsearch:{[x]
  //// the transpose requires equal-length rows
  //x:@[x;where not linesize=count each x;{linesize#0b}];
  //// we are going to work column-wise using row-oriented code, so transpose
  //if[y;x:1+:/x];
  // alternating lengths of runs of same colour
  r:{d:_[where differ x;x];count each d}each x;
  // indices of 1 1 3 1 1 runs (each being one row in finder pattern's kernel)
  c1:{-1+(`char$`int$37+12*ratios each x)ss\:"1I)1"} r;
  c:raze {[x;y] x,/:y}'[til[count c1];c1];
  // where each run begins
  o:0,/:sums each r;
  pb:c[;0],'o ./:c;
  //c[;1]+:5;
  pe:c[;0],'o ./:c+\:0 5;
  d:`long$floor 0.5*pe-pb;

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

// returns a dict of coordinates of all detected finder patterns;
// the value is the size of the pattern (centred around its coords)
pat:{
  // row-wise pattern search
  d:patsearch x;
  // column-wise pattern search (using transposed lines)
  e:patsearch 1+:/x;
  // swap coordinates of column-wise search bringing them to common basis
  e:(reverse each key e)!reverse each value e;
  // combine two dicts discarding entries that have a zero coord
  // (a zero means that pattern was not detected in the other direction)
  (where 0 in/:d+e)_d+e}

grp:{
  // distances between each pair of points
  m:`int${d:y-x;sqrt sum d*d}/:\:[x;x];
  // a list of coordinates for all elements of m
  c:raze (til count m),/:\:til count m;
  // keep the lower triangle of c (m is symmetrical)
  c:c where {x[0]>x[1]} each c;
  // order of coordinates for enumerating m in ascending order
  o:iasc m ./:c;
  // values of m in ascending order
  v:m ./:c o;
  //grouped:group m ./:c o;
  // group segments by length
  grouped:c (where differ v)_o;
  // we want three points or more, so discard single segments
  grouped:grouped where 1<count each grouped;
  // q))grouped
  // ((6 5;9 8);(1 0;2 0;4 3;5 3;7 6;8 6;10 9;11 9);(4 2;7 5;10 8)..
  bitmaps:{{x[y]:11b;x}[x#0b;]each y}[count m;]each grouped;
  // q))bitmaps
  // ((000001100000b;000000001100b);(110000000000b;101000000000b;
  // for each tuple, work out which points appears multiple times
  pivots:{1<sum each flip x}each bitmaps;
  // q))pivots
  // (000000000000b;100100100100b;
  brk
  }

// returns a list of QR codes detected in a file
decode:{ grp key pat digitise readFile x }

if[not null .z.f;
  args:.Q.opt .z.x;
  file:args`file;
  if[1>count file;file:enlist"solutions.txt"];
  show decode each file;
  exit 0;];
