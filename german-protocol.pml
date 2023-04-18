/* ************** */
/* Initialization */
/* ************** */

/* Type initialization */

mtype:cache_state = { I, S, M };
mtype:req = { ReqS, ReqM, None };
mtype:mcout = { GntS, GntM, Inv };
mtype:invack = { InvAck };
mtype:tracker_type = { GntSent, InvSent, Idle };
mtype:dog = { reset };

/* Cache state variable initialization */

bool go_I[2];
mtype:cache_state cst[2] = I;

/* Memory controller state variable initialization */

mtype:req cur_req = None;
int cur_src = -1;
bool write_epoch = false;
mtype:tracker_type tracker[2] = Idle;

/* Channel initialization */

chan Ch_1[2] = [1] of { mtype:req };
chan Ch_2[2] = [1] of { mtype:mcout };
chan Ch_3[2] = [1] of { mtype:invack };

/* Watchdog channel for timeout claims */

chan guard = [1] of { mtype:dog };

/* ********* */
/* Processes */
/* ********* */

/* Channel 1 */

/* Caches make requests */

active proctype Ch_1_send()
{
  do

    /* Cache 1 sends ReqS */

    :: atomic{                 
      (empty(Ch_1[0]) && cst[0] == I) ->
      Ch_1[0]!ReqS
    }
       
       /* Cache 1 sends ReqM */
       
    :: atomic{             
      (empty(Ch_1[0]) && (cst[0] == I || cst[0] == S)) ->
      Ch_1[0]!ReqM
    }

       /* Cache 2 sends ReqS */
       
    :: atomic{               
      (empty(Ch_1[1]) && cst[1] == I) ->
      Ch_1[1]!ReqS
    }

       /* Cache 2 sends ReqM  */

    :: atomic{               
      (empty(Ch_1[1]) && (cst[1] == I || cst[1] == S)) ->
      Ch_1[1]!ReqM
    }
       
  od
}

/* If cache has a request and MC is not currently */
/* serving a request, then MC reads the request and */
/* updates cur_src */

active proctype Ch_1_recv()
{
  do
    
    :: atomic{
      (nempty(Ch_1[0]) && cur_req == None) ->
      Ch_1[0]?cur_req;
      cur_src = 1
    }

    :: atomic{
      (nempty(Ch_1[1]) && cur_req == None) ->
      Ch_1[1]?cur_req;
      cur_src = 2
    }
       
  od
}

/* Channel 2 */

/* MC grants requests and sends invalidation messages */

active proctype Ch_2_send()
{
  do

    /* Send GntS to Cache 1 */

    :: atomic{                     
      (empty(Ch_2[0])
       && cur_src == 1
       && cur_req == ReqS
       && write_epoch == false) ->
      Ch_2[0]!GntS;
      tracker[0] = GntSent;
      cur_req = None
    }

       /* Send GntM to Cache 1 */

    :: atomic{   
      (empty(Ch_2[0])
       && cur_src == 1
       && cur_req == ReqM
       && write_epoch == false
       && tracker[0] == Idle
       && tracker[1] == Idle) ->
      Ch_2[0]!GntM;
      tracker[0] = GntSent;
      cur_req = None;
      write_epoch = true
    }

       /* Send Inv to Cache 1 */

    :: atomic{
      (empty(Ch_2[0])
       && tracker[0] == GntSent
       && ((cur_req == ReqM) || (cur_req == ReqS && write_epoch))) ->
      Ch_2[0]!Inv;
      tracker[0] = InvSent
    }

       /* Send GntS to Cache 2 */

    :: atomic{                  
      (empty(Ch_2[1])
       && cur_src == 2
       && cur_req == ReqS
       && write_epoch == false) ->
      Ch_2[1]!GntS;
      tracker[1] = GntSent;
      cur_req = None
    }

       /* Send GntM to Cache 2 */

    :: atomic{                    
      (empty(Ch_2[1])
       && cur_src == 2
       && cur_req == ReqM
       && write_epoch == false
       && tracker[0] == Idle
       && tracker[1] == Idle) ->
      Ch_2[1]!GntM;
      tracker[1] = GntSent;
      cur_req = None;
      write_epoch = true
    }

       /* Send Inv to Cache 2 */
       
    :: atomic{                   
      (empty(Ch_2[1])
       && tracker[1] == GntSent
       && ((cur_req == ReqM) || (cur_req == ReqS && write_epoch))) ->
      Ch_2[1]!Inv;
      tracker[1] = InvSent
    }
       
  od
}

/* Caches recieve grant and invaliadation messages */
/* in channel 2 and update state.  */

active proctype Ch_2_recv()
{
  do

    :: atomic{
      nempty(Ch_2[0]) ->
      if
	:: Ch_2[0]?[GntM] ->
	   Ch_2[0]?GntM;
	   cst[0] = M
	:: Ch_2[0]?[GntS] ->
	   Ch_2[0]?GntS;
	   cst[0] = S
	:: else ->
	   Ch_2[0]?Inv;
	   cst[0] = I;
	   go_I[0] = true
      fi
    }

    :: atomic{
      nempty(Ch_2[1]) ->
      if
	:: Ch_2[1]?[GntM] ->
	   Ch_2[1]?GntM;
	   cst[1] = M
	:: Ch_2[1]?[GntS] ->
	   Ch_2[1]?GntS;
	   cst[1] = S
	:: else ->
	   Ch_2[1]?Inv;
	   cst[1] = I;
	   go_I[1] = true
      fi
    }

  od
}

/* Channel 3 */

/* Caches send InvAcks and MC receives */

active proctype Ch_3_send()
{
  do

    :: atomic{
      (empty(Ch_3[0]) && go_I[0]) ->
      Ch_3[0]!InvAck;
      tracker[0] = InvSent;
      go_I[0] = false
    }

    :: atomic{
      (empty(Ch_3[1]) && go_I[1]) ->
      Ch_3[1]!InvAck;
      tracker[1] = InvSent;
      go_I[1] = false
    }

  od
}

/* MC receives InvAck from channel and removes it from sharers */

active proctype Ch_3_recv()
{
  do

    :: atomic{
      nempty(Ch_3[0]) ->
      Ch_3[0]?InvAck;
      tracker[0] = Idle
    }

    :: atomic{
      nempty(Ch_3[1]) ->
      Ch_3[1]?InvAck;
      tracker[1] = Idle
    }
       
  od
}

/* MC end of write epoch process */

active proctype end_of_wr_epoch()
{
  do
    :: atomic{
      (write_epoch
       && tracker[0] == Idle
       && tracker[1] == Idle) ->
      write_epoch = false
    }
  od
}

/* watchdog */

active proctype watchdog()
{
  do
    :: timeout -> guard!reset
  od
}

/* ****** */
/* Claims */
/* ****** */

/* First never claim below checks that if cache coherence property holds in every state, */
/* then no deadlock occurs. */

/* never { */
/*   do */
/*     :: assert( */
/*       !( */
/* 	( cst[0] != M || cst[1] == I ) */
/* 	&& ( cst[1] != M || cst[0] == I ) */
/*       ) */
/*       || timeout */
/*     ) */
/*   od */
/* } */


/* Second never claim is the cache coherence property */

/* never { */
/*   do */
/*     :: assert( cst[0] != M || cst[1] == I ) */
/*   od */
/* } */
