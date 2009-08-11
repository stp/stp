#!/usr/bin/perl -w

use strict;
for(my $vars=4; $vars <= 256;$vars=$vars*2) {
    my $form = 32;
    my $bits = 32;
    #for(my $vars=1; $vars <= 32;$vars++) {
	#for(my $bits=4; $bits <= 256;) {
	    system("/bin/sh", "-c", "./testgen.pl -nv $vars -fv $vars -nf $form -b $bits >& form_$form.var_$vars.bits_$bits.cvc");
	    #$bits = $bits*2;
	#}
    #}
}

