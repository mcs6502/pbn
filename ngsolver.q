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

// 0i -> `int$()
// 1i -> ,1i
// 2 1i -> 2 1i
wrapClue:{[x]
  :$[-6h=type x;$[0i=x;`int$();enlist x];x]
  };

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

\d .

// creates initial state if not set in file
initPuzzle:{[p]
  if[not any`state=key p;
    p[`state]:p[`height`width]#" "];
  :p;
  };

solvePuzzle:{[p]
  p:initPuzzle p;
  :p
  };

showPuzzle:{[p] show p`state}

processFile:{[x] showPuzzle solvePuzzle .non.parsePuzzle read0 hsym`$x};

args:.Q.opt .z.x;
if[not null .z.f;
  if[1>count args`file;
    -2"Usage: ",string[.z.f]," -file puzzle.non";
    exit 1];
  processFile each args`file;
  exit 0];
