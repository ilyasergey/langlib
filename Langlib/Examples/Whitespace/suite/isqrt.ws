{Conformance_suite:_isqrt._Integer_square_roots_of_six_numbers.}{Heap:_0_=_k,_1_=_n,_2_=_r;_the_six_inputs_live_at_10_through_15.}{The_loop_guard_multiplies,_which_is_the_point_of_the_program.}[push_10]   	 	 
[push_0]    
[store]		 [push_11]   	 		
[push_1]   	
[store]		 [push_12]   		  
[push_15]   				
[store]		 [push_13]   		 	
[push_16]   	    
[store]		 [push_14]   			 
[push_17]   	   	
[store]		 [push_15]   				
[push_200]   		  	   
[store]		 [push_0]    
[push_0]    
{k_:=_0}[store]		 [label_outer]
  		
[push_1]   	
[push_10]   	 	 
[push_0]    
[retrieve]			[add]	   [retrieve]			{n_:=_a[k]}[store]		 [push_2]   	 
[push_0]    
{r_:=_0}[store]		 [label_inner]
  		 
[push_1]   	
[retrieve]			[push_2]   	 
[retrieve]			[push_1]   	
[add]	   [dup] 
 {(r+1)_squared}[mul]	  
{n_-_(r+1)^2}[sub]	  	[jn_innerdone]
					
[push_2]   	 
[push_2]   	 
[retrieve]			[push_1]   	
[add]	   {r_:=_r_+_1}[store]		 [jump_inner]
 
		 
[label_innerdone]
  			
[push_2]   	 
[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   [store]		 [push_0]    
[retrieve]			[push_6]   		 
[sub]	  	[jz_done]
	 		  
[jump_outer]
 
		
[label_done]
  		  
[halt]


