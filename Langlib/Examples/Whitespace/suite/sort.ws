{Conformance_suite:_sort._Insertion_sort_of_eight_numbers.}{Heap:_the_array_at_0_through_7,_then_i,_j_and_t_at_100_to_102.}{A_computed_index_on_both_sides_of_an_assignment,_which_is_what_this}{program_is_for.}[push_0]    
[push_5]   	 	
[store]		 [push_1]   	
[push_2]   	 
[store]		 [push_2]   	 
[push_9]   	  	
[store]		 [push_3]   		
[push_1]   	
[store]		 [push_4]   	  
[push_5]   	 	
[store]		 [push_5]   	 	
[push_6]   		 
[store]		 [push_6]   		 
[push_0]    
[store]		 [push_7]   			
[push_7]   			
[store]		 [push_100]   		  	  
[push_1]   	
{i_:=_1}[store]		 [label_outer]
  		
[push_101]   		  	 	
[push_100]   		  	  
[retrieve]			{j_:=_i}[store]		 [label_inner]
  		 
[push_101]   		  	 	
[retrieve]			{j_=_0:_nothing_further_left_to_compare}[jz_innerdone]
	 			
[push_101]   		  	 	
[retrieve]			{a[j]}[retrieve]			[push_101]   		  	 	
[retrieve]			[push_1]   	
[sub]	  	{a[j-1]}[retrieve]			{a[j]_-_a[j-1]}[sub]	  	[jn_swapem]
				  
[jump_innerdone]
 
			
[label_swapem]
  		  
[push_102]   		  		 
[push_101]   		  	 	
[retrieve]			[push_1]   	
[sub]	  	[retrieve]			{t_:=_a[j-1]}[store]		 [push_101]   		  	 	
[retrieve]			[push_1]   	
[sub]	  	[push_101]   		  	 	
[retrieve]			[retrieve]			{a[j-1]_:=_a[j]}[store]		 [push_101]   		  	 	
[retrieve]			[push_102]   		  		 
[retrieve]			{a[j]_:=_t}[store]		 [push_101]   		  	 	
[push_101]   		  	 	
[retrieve]			[push_1]   	
[sub]	  	{j_:=_j_-_1}[store]		 [jump_inner]
 
		 
[label_innerdone]
  			
[push_100]   		  	  
[push_100]   		  	  
[retrieve]			[push_1]   	
[add]	   [store]		 [push_100]   		  	  
[retrieve]			[push_8]   	   
[sub]	  	[jn_outer]
				
[push_100]   		  	  
[push_0]    
[store]		 [label_printloop]
  		 	
[push_100]   		  	  
[retrieve]			[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_100]   		  	  
[push_100]   		  	  
[retrieve]			[push_1]   	
[add]	   [store]		 [push_100]   		  	  
[retrieve]			[push_8]   	   
[sub]	  	[jn_printloop]
				 	
[halt]


