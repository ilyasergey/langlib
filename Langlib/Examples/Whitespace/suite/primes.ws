{Conformance_suite:_primes._The_primes_below_30,_by_trial_division.}{Heap:_0_=_candidate,_1_=_divisor,_2_=_the_"still_prime"_flag.}{A_doubly_nested_loop_with_a_boolean_carried_between_them.}[push_0]    
[push_2]   	 
[store]		 [label_outer]
  		
[push_2]   	 
[push_1]   	
{prime_:=_1}[store]		 [push_1]   	
[push_2]   	 
{d_:=_2}[store]		 [label_inner]
  		 
[push_0]    
[retrieve]			[push_1]   	
[retrieve]			[dup] 
 [mul]	  
{candidate_-_d*d}[sub]	  	[jn_innerdone]
					
[push_0]    
[retrieve]			[push_1]   	
[retrieve]			[mod]	 		[jz_notprime]
	 		  
[push_1]   	
[push_1]   	
[retrieve]			[push_1]   	
[add]	   {d_:=_d_+_1}[store]		 [jump_inner]
 
		 
[label_notprime]
  		  
[push_2]   	 
[push_0]    
{prime_:=_0}[store]		 [label_innerdone]
  			
[push_2]   	 
[retrieve]			[jz_skip]
	 		 	
[push_0]    
[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [label_skip]
  		 	
[push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   [store]		 [push_0]    
[retrieve]			[push_30]   				 
[sub]	  	[jn_outer]
				
[halt]


