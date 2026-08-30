{Conformance_suite:_divmod._Euclidean_division_at_all_four_sign_pairs.}{This_is_the_one_program_whose_answer_whitespace_cannot_give_directly.}{Whitespace's_div_and_mod_FLOOR_(docs/whitespace/spec.md,_decision_2):}{the_remainder_takes_the_sign_of_the_divisor._Turpentine's_are}{EUCLIDEAN:_the_remainder_is_never_negative._The_two_agree_whenever_the}{divisor_is_positive_and_differ_when_it_is_negative,_and_the_fix_is}{a_ediv_b_=_-(a_fdiv_-b)_a_emod_b_=_a_fmod_-b}{both_of_which_follow_from_a_=_(a_ediv_b)_*_b_+_a_emod_b_with}{0_<=_a_emod_b_<_|b|._The_two_subroutines_below_test_the_divisor's_sign}{with_jn_and_take_that_branch_only_when_it_is_negative.}[push_17]   	   	
[push_5]   	 	
[call_ediv]
 			
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_17]   	   	
[push_5]   	 	
[call_emod]
 			 
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_neg17]  		   	
[push_5]   	 	
[call_ediv]
 			
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_neg17]  		   	
[push_5]   	 	
[call_emod]
 			 
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_17]   	   	
[push_neg5]  		 	
[call_ediv]
 			
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_17]   	   	
[push_neg5]  		 	
[call_emod]
 			 
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_neg17]  		   	
[push_neg5]  		 	
[call_ediv]
 			
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_neg17]  		   	
[push_neg5]  		 	
[call_emod]
 			 
[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [halt]


[label_ediv]
  		
[dup] 
 [jn_edivneg]
					
[div]	 	 [ret]
	
[label_edivneg]
  			
[push_0]    
[swap] 
	{the_divisor's_absolute_value}[sub]	  	[div]	 	 [push_0]    
[swap] 
	{and_negate_the_quotient}[sub]	  	[ret]
	
[label_emod]
  		 
[dup] 
 [jn_emodneg]
				  
[mod]	 		[ret]
	
[label_emodneg]
  		  
[push_0]    
[swap] 
	[sub]	  	{the_remainder_needs_no_sign_fix}[mod]	 		[ret]
	
