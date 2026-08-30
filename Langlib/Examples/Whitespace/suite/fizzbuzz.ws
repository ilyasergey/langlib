{Conformance_suite:_fizzbuzz._FizzBuzz_to_20.}{Heap:_0_=_i._Three_modulo_tests_in_the_order_that_makes_the_chain_work.}[push_0]    
[push_1]   	
[store]		 [label_loop]
  		
[push_0]    
[retrieve]			[push_15]   				
[mod]	 		[jz_fizzbuzz]
	 		 
[push_0]    
[retrieve]			[push_3]   		
[mod]	 		[jz_fizz]
	 			
[push_0]    
[retrieve]			[push_5]   	 	
[mod]	 		[jz_buzz]
	 		  
[push_0]    
[retrieve]			[outnum]	
 	[jump_endline]
 
		 	
[label_fizzbuzz]
  		 
[put_F]   	   		 
[outchar]	
  [put_i]   		 	  	
[outchar]	
  [put_z]   				 	 
[outchar]	
  [put_z]   				 	 
[outchar]	
  [put_B]   	    	 
[outchar]	
  [put_u]   			 	 	
[outchar]	
  [put_z]   				 	 
[outchar]	
  [put_z]   				 	 
[outchar]	
  [jump_endline]
 
		 	
[label_fizz]
  			
[put_F]   	   		 
[outchar]	
  [put_i]   		 	  	
[outchar]	
  [put_z]   				 	 
[outchar]	
  [put_z]   				 	 
[outchar]	
  [jump_endline]
 
		 	
[label_buzz]
  		  
[put_B]   	    	 
[outchar]	
  [put_u]   			 	 	
[outchar]	
  [put_z]   				 	 
[outchar]	
  [put_z]   				 	 
[outchar]	
  [label_endline]
  		 	
[put_LF]   	 	 
[outchar]	
  [push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   [store]		 [push_0]    
[retrieve]			[push_21]   	 	 	
[sub]	  	[jz_done]
	 			 
[jump_loop]
 
		
[label_done]
  			 
[halt]


