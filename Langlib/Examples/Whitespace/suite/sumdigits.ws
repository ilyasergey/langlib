{Conformance_suite:_sumdigits._Digit_sums_of_four_numbers.}{Heap:_0_=_k,_1_=_n,_2_=_s;_the_four_inputs_at_10_through_13.}{Divide_and_modulo_by_ten,_where_a_divmod_bug_surfaces_at_once.}[push_10]   	 	 
[push_0]    
[store]		 [push_11]   	 		
[push_7]   			
[store]		 [push_12]   		  
[push_9045]   	   		 	 	 	 	
[store]		 [push_13]   		 	
[push_32767]   															
[store]		 [push_0]    
[push_0]    
[store]		 [label_outer]
  		
[push_1]   	
[push_10]   	 	 
[push_0]    
[retrieve]			[add]	   [retrieve]			{n_:=_a[k]}[store]		 [push_2]   	 
[push_0]    
{s_:=_0}[store]		 [label_inner]
  		 
[push_1]   	
[retrieve]			{every_input_here_is_non-negative}[jz_innerdone]
	 			
[push_2]   	 
[push_2]   	 
[retrieve]			[push_1]   	
[retrieve]			[push_10]   	 	 
[mod]	 		[add]	   {s_:=_s_+_n_mod_10}[store]		 [push_1]   	
[push_1]   	
[retrieve]			[push_10]   	 	 
[div]	 	 {n_:=_n_/_10}[store]		 [jump_inner]
 
		 
[label_innerdone]
  			
[push_2]   	 
[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   [store]		 [push_0]    
[retrieve]			[push_4]   	  
[sub]	  	[jz_done]
	 		  
[jump_outer]
 
		
[label_done]
  		  
[halt]


