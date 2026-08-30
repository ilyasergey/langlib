{Conformance_suite:_binary._Five_numbers_written_in_binary.}{Heap:_the_bit_stack_at_0_through_15,_k/n/m/i_at_100_to_103,_and_the}{five_inputs_at_200_through_204._The_bits_come_out_least_significant}{first,_so_they_are_stacked_and_then_read_back_downwards.}[push_200]   		  	   
[push_0]    
[store]		 [push_201]   		  	  	
[push_1]   	
[store]		 [push_202]   		  	 	 
[push_5]   	 	
[store]		 [push_203]   		  	 		
[push_64]   	      
[store]		 [push_204]   		  		  
[push_1000]   					 	   
[store]		 [push_100]   		  	  
[push_0]    
[store]		 [label_outer]
  		
[push_101]   		  	 	
[push_200]   		  	   
[push_100]   		  	  
[retrieve]			[add]	   [retrieve]			{n_:=_vals[k]}[store]		 [push_102]   		  		 
[push_0]    
{m_:=_0}[store]		 [push_101]   		  	 	
[retrieve]			{zero_has_no_bits,_and_still_prints_one_digit}[jz_zero]
	 		 
[label_bitloop]
  			
[push_101]   		  	 	
[retrieve]			[jz_bitdone]
	 		  
[push_102]   		  		 
[retrieve]			[push_101]   		  	 	
[retrieve]			[push_2]   	 
[mod]	 		{bits[m]_:=_n_mod_2}[store]		 [push_101]   		  	 	
[push_101]   		  	 	
[retrieve]			[push_2]   	 
[div]	 	 {n_:=_n_/_2}[store]		 [push_102]   		  		 
[push_102]   		  		 
[retrieve]			[push_1]   	
[add]	   {m_:=_m_+_1}[store]		 [jump_bitloop]
 
			
[label_bitdone]
  		  
[push_103]   		  			
[push_102]   		  		 
[retrieve]			{i_:=_m}[store]		 [label_printloop]
  		 	
[push_103]   		  			
[retrieve]			[jz_endline]
	 			 
[push_103]   		  			
[push_103]   		  			
[retrieve]			[push_1]   	
[sub]	  	[store]		 [push_103]   		  			
[retrieve]			[retrieve]			[outnum]	
 	[jump_printloop]
 
		 	
[label_zero]
  		 
[put_0]   		    
[outchar]	
  [label_endline]
  			 
[put_LF]   	 	 
[outchar]	
  [push_100]   		  	  
[push_100]   		  	  
[retrieve]			[push_1]   	
[add]	   [store]		 [push_100]   		  	  
[retrieve]			[push_5]   	 	
[sub]	  	[jz_done]
	 				
[jump_outer]
 
		
[label_done]
  				
[halt]


