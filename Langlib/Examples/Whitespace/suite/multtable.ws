{Conformance_suite:_multtable._A_five-by-five_table,_tab_separated.}{Two_nested_counted_loops,_both_of_which_print.}{row}[push_1]   	
[label_rows]
  		
{col}[push_1]   	
[label_cols]
  		 
{row}[copy_1] 	  	
{col}[copy_1] 	  	
[mul]	  
[outnum]	
 	[dup] 
 [push_5]   	 	
[sub]	  	{no_tab_after_the_last_column}[jz_endrow]
	 			
[put_TAB]   	  	
[outchar]	
  [label_aftertab]
  		  
[push_1]   	
{col_:=_col_+_1}[add]	   [dup] 
 [push_6]   		 
[sub]	  	[jz_colsdone]
	 		 	
[jump_cols]
 
		 
[label_endrow]
  			
[jump_aftertab]
 
		  
[label_colsdone]
  		 	
{discard_col}[drop] 

[put_LF]   	 	 
[outchar]	
  [push_1]   	
{row_:=_row_+_1}[add]	   [dup] 
 [push_6]   		 
[sub]	  	[jz_done]
	 			 
[jump_rows]
 
		
[label_done]
  			 
[drop] 

[halt]


