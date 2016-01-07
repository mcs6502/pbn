// ngsolver.q -- a nonogram solver 
/
Copyright (c) 2015 Igor Mironov. All rights reserved. 
Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met: 

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer. 

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution. 

3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission. 

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE. 
\

\d .non

// "1" -> 1i; "1,2" -> 1 2i
lexInt:{[x] :$[x like"*,*";"I"$/:","vs x;"I"$x]};

// "\"foo bar\"" -> "foo bar"
lexStr:{[x] :-1_1_x};

// "foo" -> `foo
lexSym:{[x] :`$x};

lex:{[words]
  if[not count words;:()];
  word:first words;
  $[not count word;
      :lex 1_words;
    word like"[0-9]*";
      :enlist[lexInt[word]],lex 1_words;
    word like"\"*";
      [ends:where(words like"*\"")&not words like"*\\\"";
      len:1+first ends where(ends>0)|1<count each words ends;
      :enlist[lexStr" "sv len #words],lex len _words];
    :enlist[lexSym word],lex 1_words]
  };

lexLines:{[x] :lex each" "vs'x};

// group values by name: (`height;20i) (`rows;0i;1 1i;1 1i;6 1i)
flatten:{[tokens]
  symbols:-11h=type each tokens;
  :(where symbols)_tokens
  };

// (`height;20i) -> height|20i
toDict:{[pairs]
  k:first each pairs;
  v:1_'pairs;
  unwrap:where 1=count each v;
  v[unwrap]:first each v unwrap;
  :k!v
  };

// 1i -> ,1i
// 2 1i -> 2 1i
wrapClue:{(),x}

parsePuzzle:{[lines]
  p:toDict flatten raze lexLines lines;
  p[`rows]:wrapClue each p`rows;
  p[`columns]:wrapClue each p`columns;
  // slice the goal and state into width-sized pieces
  if[any`goal=key p;
    p[`goal]:p[`width]cut p`goal];
  // original file format does not have the state
  if[any`state=key p;
    p[`state]:p[`width]cut p`state];
  :p
  };

\d .ng

// qidioms #144. histogram
hist:{@[x;y;+;1]}

// choose k from list of n
comb:{[k;l]
  n:count l;
  $[k<1;();
    k=1;enlist each l;
    k<n;raze {y[z],/:comb[x;(1+z)_y]}[k-1;l] each til 1+n-k;
    enlist l]}

// multichoose (multisets of length y on x symbols)
arrange:{$[x>0;hist[y#0] each comb[x;til x+y-1]-\:til x;enlist y#0]}

fillgaps:{n:count y; k:$[n>2;n-2;0]; v:$[n>1;raze(1;k;1)#'0 1 0;enlist 0]; v+/:arrange[x-k+sum y;n]}
// (1 2 0;3 4 0) -> ".MMM..MMMM"
expand:{v:raze flip(x;y); raze v#'count[v]#".M"}
// generate all possible lines of length n for clue c
genlines:{[n; c] expand[;c] each fillgaps[n;c]}
pickgood:{all each null[x]|/:x=/:y}
// qidioms #142. binomial coefficients
fac:{[n]$[n>1;n*fac[n-1];1]}
binn:{[n;k]fac[n]%fac[n-k]*fac[k]}
// http://mathworld.wolfram.com/Multichoose.html
maxlines:{binn[`float$x+y-1;`float$y-1]}

\d .rb

// CHRIS OKASAKI (1999). Red-black trees in a functional setting.
// Journal of Functional Programming, 9, pp 471-477

cmp:{n:(count x)&count y;i:first where not(n#x)=n#y;$[not null i;z[x[i];y i];z[count[x];count y]]}
lt:cmp[;;<]
empty:`E
member:{if[y~`E;:0b];e:y`e;$[lt[x;e];member[x;y`a];x~e;1b;member[x;y`b]]}
makeBlack:{x[`colour]:`B;x}
ins:{if[y~`E;:`colour`a`e`b!(`R;`E;x;`E)];e:y`e;$[lt[x;e];balance`colour`a`e`b!(y`colour;ins[x;y`a];e;y`b);x~e;`colour`a`e`b!(y`colour;y`a;x;y`b);balance`colour`a`e`b!(y`colour;y`a;e;ins[x;y`b])]}
insertNode:{[x;s] makeBlack ins[x;s]}
isColour:{$[99h~type y;$[x~y`colour;1b;0b];0b]}
isBlack:isColour[`B]
isRed:isColour[`R]
balance:{$[isBlack x;$[isRed a:x`a;$[isRed a`a;`colour`a`e`b!(`R;(`colour`a`e`b!(`B;(a`a)`a;(a`a)`e;(a`a)`b));a`e;`colour`a`e`b!(`B;a`b;x`e;x`b));isRed a`b;`colour`a`e`b!(`R;`colour`a`e`b!(`B;a`a;a`e;(a`b)`a);(a`b)`e;`colour`a`e`b!(`B;(a`b)`b;x`e;x`b));x];isRed b:x`b;$[isRed b`a;`colour`a`e`b!(`R;`colour`a`e`b!(`B;x`a;x`e;(b`a)`a);(b`a)`e;`colour`a`e`b!(`B;(b`a)`b;b`e;b`b));isRed b`b;`colour`a`e`b!(`R;`colour`a`e`b!(`B;x`a;x`e;b`a);b`e;`colour`a`e`b!(`B;(b`b)`a;(b`b)`e;(b`b)`b));x];x];x]}

\d .

initPuzzle:{[p]
  width:p`width;
  height:p`height;

  // unfold the puzzle into one dimension
  clues:p[`rows],p`columns;
  coords:((til height),\:(::)),(::),/:til width;
  ids:til count clues;
  labels:(`$"row ",/:string 1+til height),`$"col ",/:string 1+til width;
  sizes:(height#width),width#height;

  t:([id:ids] clue:clues; coord:coords; label:labels; size:sizes);

  // properly terminate each clue
  t:update clue:{i:where not 0=last each x; x[i]:x[i],\:0i; :x} clue from t;

  // calculate the number of "stretchy" blanks that are to be apportioned
  t:update gap:size-{n:count x; $[n>2;n-2;0]+sum x} each clue from t;

  // calculate static solution complexity of each line
  t:update weight:{xlog[2] .ng.maxlines[x;count y]}'[gap;clue] from t;
  t:update %[weight-min weight;max weight-min weight] from t;
  t:update ncombs:{.ng.maxlines[x;count y]}'[gap;clue] from t;

  // check that each clue is within its size limit
  toolong:exec label from t where gap<0;
  if[count toolong; -2"Clue too long: ",", "sv string toolong; :()];

  // make lists of intersecting lines that can be affected by edits
  t:update peers:{$[z<y; y+til x; til y]}[width;height]each id from t;

  // pre-generate all lines
  t:update lines:.ng.genlines'[size;clue] from t;

  // create initial state if not set in file
  if[not any`state=key p;
    p[`state]:(height;width)#" "];

  // a puzzle is the initial state plus the rules for transforming it
  (p`state;t)
  };

solvePuzzle:{[p]
  p:initPuzzle p;
  if[()~p;:p];
  s:p[0];
  t:p[1];
  .ng.var.states:.rb.empty;
  .ng.var.t:.z.t;
  .ng.var.dt:0;
  .ng.var.i:0;
  .ng.var.j:0;
  .ng.var.nsol:0;
  .ng.var.nstates:0;
  solve[t;s]
  }


applyLine:{[t;s;d;li]
  //-1"### g";
  l:d[`lines][li];
  //-1 l;
  i:d`coord;
  //-1"### i";
  o:.[s;i];
  // update the state with the new line
  s[i[0];i[1]]:l;
  //-1"### k";
  // check peers where cells transition from space to blank or mark
  affectedPeers:(d`peers) where (null o) & not null l;
  //-1", "sv string each affectedPeers;
  //-1"### b";
  haveSolutions:{[s;d]
    //t0:.z.t;
    goodLines:.ng.pickgood[s . d`coord;d`lines];
    //dt:.z.t-t0;
    //.ng.var.dt:.ng.var.dt+dt;
    //-1"### d";
    //show goodLines;
    //-1 string[d`label],": ncombs=",string[d`ncombs],", nlines=",string ns;
    any goodLines
    }[s] each select from t where id in affectedPeers;
  //show haveSolutions;
  //-1"### e";
  //if[.ng.var.nstates>15;:()];
  $[all haveSolutions;s;()]
  }

// returns id of the best line to solve next
pickNextId:{[t;s]
  // calculate the percentage of unfilled cells in each line
  foo2:select id, weight, size, unfilled:sum each null s ./:coord from t;
  foo2:update unfilled:unfilled%size from foo2;
  //-1"### c";
  // calculate the solution priority of a line as a weighted average
  // of its static solution complexity and the percentage of untouched
  // cells in it
  foo2:`priority xasc update priority:0.25*weight+3*unfilled from foo2;
  // only consider the lines that have not been solved already
  foo:select from foo2 where unfilled>0;
  first exec id from foo
  }

showStats:{
  t1:.z.t;
  dt:t1-.ng.var.t;
  if[dt>10000;
    -1"dt=",string[dt],", n=",string[.ng.var.i-.ng.var.j],
      ", i=",string[.ng.var.i],", nsol=",string[.ng.var.nsol];
    .ng.var.dt:0;.ng.var.j:.ng.var.i;.ng.var.t:t1;];
  }

foundSolution:{[s]
  {.ng.var.h x,"\n"}each s;
  if[.ng.var.nsol;.ng.var.h"\n"];
  .ng.var.nsol:.ng.var.nsol+1;
  }

solve:{[t;s]
  .ng.var.i:.ng.var.i+1;
  showStats[];
  if[not count s;:()];
  .ng.var.nstates:.ng.var.nstates+1;
  //-1"### b nstates=",string .ng.var.nstates;
  nextid:pickNextId[t;s];
  //-1"### c";
  if[null nextid;foundSolution[s];:()];
  //-1"### d";
  d:exec from t where id=nextid;
  //-1"### d=";show d;
  t0:.z.t;
  goodlines:.ng.pickgood[s . d`coord;d`lines];
  dt:.z.t-t0;
  .ng.var.dt:.ng.var.dt+dt;
  //-1"goodlines=",string sum goodlines;
  nextstates:applyLine[t;s;d] peach where goodlines;
  //-1"#nextstates=",string count nextstates;
  //show first each nextstates;
  solve[t] each nextstates;
  };

showPuzzle:{[p] p}

processFile:{[x] .ng.var.h:hopen`:solutions.txt; showPuzzle solvePuzzle .non.parsePuzzle read0 hsym`$x; hclose .ng.var.h};

args:.Q.opt .z.x;
if[not null .z.f;
  if[1>count args`file;
    -2"Usage: ",string[.z.f]," -file puzzle.non";
    exit 1];
  processFile each args`file;
  exit 0];
