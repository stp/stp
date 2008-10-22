#!/usr/bin/perl -w

# Generate random  bitvector fromulas

use strict;
use POSIX;
use Math::BigInt ':constant';

#my @operators = ("=", "/=", "BVLT", "BVGT", "BVLE", "BVGE", "BVSLT", "BVSLE", "BVSGE", "BVSGT");
my @operators = ("=", "/=");

my $usageString = "Generate random  bitvector fromulas\n\n" .
"Usage:

  testgen.pl [ options ]

Options are:\n" .
"  -h              Print this message and exit
  -nv num_vars     Total number of variables
  -fv num_vars     Average number of vars in each formula
  -nf num_form     Number of formulas
  -c  const_size   Max. absolute size of the constant on the RHS
  -co coeff_size   Max. absolute coefficient size on the LHS
  -b  bits         Number of bits per variable";

my ($numVars, $numVarsInFormula, $numFormulas, $maxConstSize, $bitspervar);

# Process command line options
for(my $i=0; $i <= $#ARGV; $i++) {
    if($ARGV[$i] eq "-h") {
        print("Usage: ", $usageString, "\n");
	exit(0);
    } elsif($ARGV[$i] =~ /^(-nv|-fv|-nf|-b|-f)$/) {
        my $c = $ARGV[$i];
	$i++;
	if($i <= $#ARGV) {
	    $numVars = $ARGV[$i] if($c eq "-nv");
	    $numVarsInFormula = $ARGV[$i] if($c eq "-fv");
	    $numFormulas = $ARGV[$i] if($c eq "-nf");
	    $bitspervar = $ARGV[$i] if($c eq "-b");
	} else {
	    print STDERR ("Option $c requires an argument.\n\n",
			  $usageString, "\n");
	    exit(1);
	}
    } else {
	print STDERR ("Option '$ARGV[$i]' is not recognized.\n",
		      $usageString, "\n");
	exit(1);
    }
}


# Check if all the required options are specified

{
    my @undefined = ();
    if(!defined($numVars)) {
	push @undefined, "-nv";
    }
    if(!defined($numFormulas)) {
	push @undefined, "-nf";
    }
    if(!defined($bitspervar)) {
	push @undefined, "-b";
    }
    if($#undefined >= 0) {
	print STDERR ("\nERROR: These required options were not set: ",
		      join(", ", @undefined), "\n\n", $usageString, "\n");
    }
}

# Set the optional arguments to their default values if they were omitted
if(!defined($numVarsInFormula)) {
    $numVarsInFormula = ceil($numVars / 2);
}
   
# Generate an integer random number between two bounds (inclusive)
sub intrand {
    my ($low, $hi) = @_;

    my $diff = $hi - $low;
    if($diff <= 0) {
	die "intrand: hi is less or the same as low: $hi <= $low\n";
    }
    my $c = (floor(rand($diff + 0.99)) + $low);
    if($bitspervar == 4) {
	return sprintf("%01x",$c);
    }
    elsif($bitspervar == 8) {
	return sprintf("%02x",$c);
    }
    elsif($bitspervar == 16) {
	return sprintf("%04x",$c);
    }
    elsif($bitspervar == 32) {
	return sprintf("%08x",$c);
    }
    elsif($bitspervar == 64) {
	return sprintf("%016x",$c);
    }
    elsif($bitspervar == 128) {
	return sprintf("%032x",$c);
    }
    elsif($bitspervar == 256) {
	return sprintf("%064x",$c);
    }
    elsif($bitspervar == 512) {
	return sprintf("%0128x",$c);
    }
    elsif($bitspervar == 1024) {
	return sprintf("%0256x",$c);
    }
    else {
	die "intrand: number of bits per var must be one of 4,8,16,32,64,128,256\n";
    }
}

# Generate zero constant of the correct size
sub zero_const {
    my $c = 0;
    if($bitspervar == 4) {
	return sprintf("%01x",$c);
    }
    elsif($bitspervar == 8) {
	return sprintf("%02x",$c);
    }
    elsif($bitspervar == 16) {
	return sprintf("%04x",$c);
    }
    elsif($bitspervar == 32) {
	return sprintf("%08x",$c);
    }
    elsif($bitspervar == 64) {
	return sprintf("%016x",$c);
    }
    elsif($bitspervar == 128) {
	return sprintf("%032x",$c);
    }
    elsif($bitspervar == 256) {
	return sprintf("%064x",$c);
    }
    elsif($bitspervar == 512) {
	return sprintf("%0128x",$c);
    }
    elsif($bitspervar == 1024) {
	return sprintf("%0256x",$c);
    }
    else {
	die "intrand: number of bits per var must be one of 4,8,16,32,64,128,256\n";
    }
}

# number of variables
#
my @bv_vars = ();
for(my $j = 0; $j < $numVars; $j++) {
    push @bv_vars, "x$j";
}

for(my $j = 0; $j < $numVars; $j++) {
    print("\n$bv_vars[$j] : BITVECTOR($bitspervar);");
}

print "\n";

# Generate each atomic formula
for(my $i = 0; $i < $numFormulas; $i++) {
    my $op = $operators[intrand(0,$#operators)];

    # Coefficients: with probability 1 - (numVarsInFormula / numVars)
    # a coefficient is 0
    my @coeff = ();

    my $c = 0;  
    my $zeroc = zero_const();
    for(my $j = 0; $j < $numVars; $j++) {
	if(rand(1) < $numVarsInFormula / $numVars) {
	    $c = intrand(0, ($bitspervar-1)**2);
	    push @coeff, "BVMULT($bitspervar,$bv_vars[$j], 0hex$c),";
	} else {
	    push @coeff, "0hex$zeroc,";
	}
    }
    my $const = intrand(0, ($bitspervar-1)**2);
    if($op eq "=") {
	print("ASSERT (BVPLUS($bitspervar,", join(" ", @coeff),"0hex$zeroc) = 0hex$const);\n");
    }
    elsif ($op eq "/=") {
	print("ASSERT (BVPLUS($bitspervar,", join(" ", @coeff),"0hex$zeroc) /= 0hex$const);\n");
    }
    else {
	print("ASSERT $op(BVPLUS($bitspervar,", join(" ", @coeff),"0hex$zeroc),0hex$const);\n");
    }
}

print "\nQUERY FALSE;\n";
