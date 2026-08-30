{Conformance_suite:_logic._Every_boolean_and_comparison_operator,_and}{no_arithmetic_worth_the_name.}{Whitespace_has_exactly_two_conditional_jumps,_jump-if-zero_and}{jump-if-negative,_so_every_comparison_here_is_built_from_a_subtraction}{and_one_of_those._Heap:_0_=_t,_1_=_f.}[push_0]    
[push_1]   	
[push_2]   	 
[call_lt]
 			
{t_:=_1_<_2}[store]		 [push_1]   	
[push_2]   	 
[push_1]   	
[call_lt]
 			
{f_:=_2_<_1}[store]		 [push_0]    
[retrieve]			{t}[call_pb]
 			 
[push_1]   	
[retrieve]			{f}[call_pb]
 			 
[push_0]    
[retrieve]			[push_1]   	
[retrieve]			[mul]	  
{t_and_f:_both_are_0_or_1,_so_this_is_a_product}[call_pb]
 			 
[push_0]    
[retrieve]			[push_1]   	
[retrieve]			[add]	   [call_tobool]
 				
{t_or_f}[call_pb]
 			 
[push_1]   	
[push_0]    
[retrieve]			[sub]	  	{not_t}[call_pb]
 			 
[push_3]   		
[push_3]   		
[call_eq]
 			  
{3_==_3}[call_pb]
 			 
[push_3]   		
[push_3]   		
[call_eq]
 			  
[push_1]   	
[swap] 
	[sub]	  	{3_!=_3}[call_pb]
 			 
[push_3]   		
[push_3]   		
[call_lt]
 			
[push_1]   	
[swap] 
	[sub]	  	{3_<=_3,_that_is_not_(3_<_3)}[call_pb]
 			 
[push_3]   		
[push_4]   	  
[call_lt]
 			
[push_1]   	
[swap] 
	[sub]	  	{3_>=_4,_that_is_not_(3_<_4)}[call_pb]
 			 
[push_2]   	 
[push_3]   		
[call_lt]
 			
{3_>_2,_that_is_2_<_3}[call_pb]
 			 
[push_2]   	 
[push_3]   		
[call_lt]
 			
{2_<_3}[call_pb]
 			 
[halt]


[label_lt]
  		
{the_caller_pushed_a_then_b,_so_this_is_a_-_b}[sub]	  	[jn_ltyes]
				 	
[push_0]    
[ret]
	
[label_ltyes]
  		 	
[push_1]   	
[ret]
	
[label_eq]
  		  
[sub]	  	[jz_eqyes]
	 			 
[push_0]    
[ret]
	
[label_eqyes]
  			 
[push_1]   	
[ret]
	
[label_tobool]
  			
[jz_tbzero]
	 				
[push_1]   	
[ret]
	
[label_tbzero]
  				
[push_0]    
[ret]
	
[label_pb]
  		 
[jz_pbfalse]
	 		   
[put_t]   			 	  
[outchar]	
  [put_r]   			  	 
[outchar]	
  [put_u]   			 	 	
[outchar]	
  [put_e]   		  	 	
[outchar]	
  [jump_pbend]
 
		  	
[label_pbfalse]
  		   
[put_f]   		  		 
[outchar]	
  [put_a]   		    	
[outchar]	
  [put_l]   		 		  
[outchar]	
  [put_s]   			  		
[outchar]	
  [put_e]   		  	 	
[outchar]	
  [label_pbend]
  		  	
[put_LF]   	 	 
[outchar]	
  [ret]
	
