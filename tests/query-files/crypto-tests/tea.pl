#!/usr/bin/perl

# the trivial TEA algorithm, STP-ized:

my $tea = <<END

#include <stdio.h>

void encrypt (uint32_t* v, uint32_t* k, uint32_t* v1) {
    uint32_t v0=v[0], sum=0, i;           /* set up */
    uint32_t delta=0x9e3779b9;                     /* a key schedule constant */
    uint32_t k0=k[0], k1=k[1], k2=k[2], k3=k[3];   /* cache key */
    for (i=0; i < 32; i++) {                       /* basic cycle start */
        sum += delta;
        v0 += ((v1<<4) + k0) ^ (v1 + sum) ^ ((v1>>5) + k1);
        v1 += ((v0<<4) + k2) ^ (v0 + sum) ^ ((v0>>5) + k3);  
    }                                              /* end cycle */
    v[0]=v0; v[1]=v1;
}

END
;

####################################


my $round = 0;


sub setup_key(){
   my $pre = "
k0,k1,k2,k3 : BITVECTOR(32);
";
   return $pre;
}


sub setup_round($){
   my $V = shift;

   my $str = "
   v_delta, v_delta_0, v0_0, v1_0: BITVECTOR(32);

   % uint32_t delta=0x9e3779b9;                     /* a key schedule constant */
   ASSERT(v_delta = 0hex9e3779b9);

   ASSERT(v_delta_0=0hex00000000);
";

   $v0 = $V . "0";
   $v1 = $V . "1";
   $str =~ s/v0/$v0/g;
   $str =~ s/v1/$v1/g;
   $V .= "_";
   $str =~ s/v_/$V/g;

   return $str;

}

sub get_round($$){
   $V = shift;
   $R = shift;
   $P = $R - 1;

   $V0 = $V . "0";
   $V1 = $V . "1";
   $VU = $V . "_";

# this looks hideous, using string replacement, but it's the cleanest way.
# I could use a better language, but having seen SMTLib I'm not going to complain about
# STP :) 

   my $str = "
   % round _R_;

   v0_R,v1_R,v_delta_R : BITVECTOR(32);

   % sum += delta;

   ASSERT(v_delta_R = BVPLUS(32,v_delta_P,v_delta));

   % v0 += ((v1<<4) + k0) ^ (v1 + sum) ^ ((v1>>5) + k1);

   v0_R_t1,v0_R_t2,v0_R_t3,v0_R_t4,v0_R_t5,v0_R_t6,v0_R_t7 : BITVECTOR(32);
   ASSERT(v0_R_t1 = BVMULT(32,v1_P,0hex00000010));
   ASSERT(v0_R_t2 = BVPLUS(32,v0_R_t1, k0));
   ASSERT(v0_R_t3 = BVPLUS(32,v1_P,v_delta_R));
   ASSERT(v0_R_t4 = BVXOR(v0_R_t2,v0_R_t3));
   ASSERT(v0_R_t5 = v1_P>>5);
   ASSERT(v0_R_t6 = BVPLUS(32,v0_R_t5,k1));
   ASSERT(v0_R = BVXOR(v0_R_t4,v0_R_t6));

   % v1 += ((v0<<4) + k2) ^ (v0 + sum) ^ ((v0>>5) + k3); 

   v1_R_t1,v1_R_t2,v1_R_t3,v1_R_t4,v1_R_t5,v1_R_t6,v1_R_t7 : BITVECTOR(32);
   ASSERT(v1_R_t1 = BVMULT(32,v0_P,0hex00000010));
   ASSERT(v1_R_t2 = BVPLUS(32,v1_R_t1, k2));
   ASSERT(v1_R_t3 = BVPLUS(32,v0_P,v_delta_R));
   ASSERT(v1_R_t4 = BVXOR(v1_R_t2,v1_R_t3));
   ASSERT(v1_R_t5 = v0_P>>5);
   ASSERT(v1_R_t6 = BVPLUS(32,v1_R_t5,k3));
   ASSERT(v1_R = BVXOR(v1_R_t4,v1_R_t6));
";

   $str =~ s/v0/$V0/g;
   $str =~ s/v1/$V1/g;
   $str =~ s/v_/$VU/g;
   $str =~ s/_R/_$R/g;
   $str =~ s/_P/_$P/g;

   return $str;
}

print setup_key(); # fixed (for now)

print setup_round("v");
print setup_round("x");

while($round++<=32){
   print get_round("v", $round);
   print get_round("x", $round);
}

my $p = $round-1; 


# Alright.  Now the meat of things.
# KEYS -- k0 through k3.  Comment them out, and we'll have to solve for them.  Comment some 
#    of them out, and you have a partial key atack.
# INITIAL STATE -- v0_0 and v0_1 -- this is the plaintext being encrypted.  Comment these out
#    to attempt to recover plaintext from ciphertext.  Possible, with a limited number of rounds,
#    and a shared key.  There's a name for this class of attack, I don't remember it.
# MULTIPLE INITIAL STATE -- x0_0 and x0_1 -- as long as you setup_round(x) and get_round(x) up
#    there, you can declare a plaintext for x and its constraints will be mixed in happily.
# INTERMEDIATE STATE -- v0_2 and v1_2 -- this is ciphertext, although insufficiently mixed
#    at this point.  Uncomment this, and plaintext, to discover the key from a plaintext/
#    ciphertext pair (very useful, very common attack class).  Or uncomment this, leaving
#    key and plaintext secret, to try to blindly recover the plaintext and key.


my $query = <<END

QUERY(
   NOT(
      %
      % KEYS 
      % (All commented out = solve for all key bits)
      %k0  = 0hex00011111 AND
      %k1  = 0hex22112222 AND 
      %k2  = 0hex33444555 AND 
      %k3  = 0hex11441144 AND
      %
      % INITIAL STATE (PLAINTEXT)
      %
      %v0_0  = 0hexeeaaeeaa AND v0_1 = 0hexdddddddd AND
      %x0_0  = 0hex12312312 AND x0_1 = 0hexdeadbeef AND
      %
      % INTERMEDIATE STATE 

      % Solve for 2 rounds of TEA
      v0_2  = 0hex7ACD453B  AND v1_2 = 0hex135DF258  AND
      x0_2  = 0hex633206CC  AND x1_2 = 0hex1D05F91F   AND

      % Solve for 3 rounds of TEA
      %v0_3  = 0hexF94878A6 AND v1_3 = 0hexA071500E AND
      %x0_3  = 0hex053594A1 AND x1_3 = 0hex4FE16098 AND

      % Solve for 4 rounds of TEA

      %v0_4  = 0hex394d8ba1 AND v1_4 = 0hexace3c536 AND
      %x0_4  = 0hex123870CB AND x1_4 = 0hexE9E34909 AND
      %
      % JUST THERE SO EVERY LINE CAN END WITH AND
      x0_0=x0_0
  
  )
);

COUNTEREXAMPLE;

END
;

print $query;

