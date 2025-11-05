$( Test: variables NOT starting with 'v', constants starting with 'v'
   Per Metamath spec section 4.2.1: symbol names are arbitrary $)

$c wff |- ( ) vtrue vimplies $.
$v cx cy cz $.

cx-is-wff $f wff cx $.
cy-is-wff $f wff cy $.
cz-is-wff $f wff cz $.

$( Axiom with constant 'vtrue' - starts with 'v' but is a CONSTANT $)
ax-vtrue $a wff vtrue $.

$( Axiom with constant 'vimplies' and variables 'cx', 'cy' $)
ax-vimpl $a wff ( vimplies cx cy ) $.

$( Simple theorem: just use vtrue constant $)
th1 $p wff vtrue $= ax-vtrue $.

$( Theorem using variable 'cx' - starts with 'c' not 'v' $)
th2 $p wff ( vimplies cx cy ) $= cx-is-wff cy-is-wff ax-vimpl $.
