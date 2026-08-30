{Conformance_suite:_sieve._The_sieve_of_Eratosthenes_below_50.}{Heap:_0_=_i,_1_=_j,_and_the_50-cell_flag_array_at_100_through_149.}{The_heap_is_integer-addressed,_so_a_computed_index_is_an_add_and_a}{store_--_the_array_costs_this_language_almost_nothing.}{The_prologue_writes_every_flag_cell_before_anything_reads_one:_the}{authors'_wspace_crashes_on_a_cell_that_was_never_stored,_so_a_faithful}{program_does_not_lean_on_a_heap_that_defaults_to_zero.}[push_0]    
[push_0]    
[store]		 [label_clear]
  		
[push_100]   		  	  
[push_0]    
[retrieve]			[add]	   [push_0]    
[store]		 [push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   [store]		 [push_0]    
[retrieve]			[push_50]   		  	 
[sub]	  	[jz_cleardone]
	 		 
[jump_clear]
 
		
[label_cleardone]
  		 
[push_0]    
[push_2]   	 
[store]		 [label_outer]
  			
[push_100]   		  	  
[push_0]    
[retrieve]			[add]	   [retrieve]			[jz_isprime]
	 		  
[jump_nextouter]
 
		 	
[label_isprime]
  		  
[push_0]    
[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_1]   	
[push_0]    
[retrieve]			[push_2]   	 
[mul]	  
{j_:=_2i,_the_first_multiple_to_strike_out}[store]		 [label_mark]
  			 
[push_1]   	
[retrieve]			[push_50]   		  	 
[sub]	  	[jn_markbody]
						
[jump_nextouter]
 
		 	
[label_markbody]
  				
[push_100]   		  	  
[push_1]   	
[retrieve]			[add]	   [push_1]   	
{composite[j]_:=_1}[store]		 [push_1]   	
[push_1]   	
[retrieve]			[push_0]    
[retrieve]			[add]	   {j_:=_j_+_i}[store]		 [jump_mark]
 
			 
[label_nextouter]
  		 	
[push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   [store]		 [push_0]    
[retrieve]			[push_50]   		  	 
[sub]	  	[jn_outer]
					
[halt]


