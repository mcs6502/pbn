# pbn

This project contains two kdb+/q programs: a solver for nonogram (_paint by numbers_, griddler) puzzles in .non format, and a decoder for QR codes.
The nonogram solver follows a straightforward cost-based search algorithm.  It is a "closed book" solution—the author had not consulted any of the available fine literature on the subject (there are faster algorithms to consider).
The QR codes' decoder contains a sort of machine vision algorithm, in the sense that it interprets the input ASCII art image as a bitmap, and attempts to recognise any QR symbols that it may contain.  The algorithm is not free-form—it requires that symbols be aligned with the axes of the image they are embedded in.  Also it does not tolerate nonlinear distortions.  Like the combinatorial solver, this program is the result of the author's own research, and is likely to contain areas for improvement.

Copyright 2015-2016, mcs6502