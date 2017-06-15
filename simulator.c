#include<stdio.h>
#include<stdlib.h>
#include<string.h>
#include<limits.h>

#define INSTRU_NO 300

//input file
char *filename="Input 2.txt";

int execute_intpc;
int execute_mul1pc;
int execute_memory1pc;

//
int cycles_done=0;
int pc_update;
int current_pc=0;

//no. of instructions read and stored in array
int no_of_instru=0;

//starting index of instructions
int pc_offset=20000;

//registers
int R[8];
int X;
int mem[10000];

//register status bit
int reg_status[9];

//physical registers
int PRF[16];
int PRF_status[16];

//REGISTER RENAMING
//free list
int free_list[16];
int AL[16];
int renamed_array[16];
int rename_table[9];

//instruction array
char instruction[INSTRU_NO][20];

//flags
int flag_zero;
int flag_halt;
int flag_done; //instructions finished
int dependent_flag;
int dependent_reg;
//flag for IQ space check
int flag_IQfull;
int flag_LSQfull;
//flag for free list
int flag_freeList;
int flag_ROBfull;
int flag_MULoccupied;

//flags for INT and MUL stall
int flag_INTstall;
int flag_MULstall;
int flag_predtaken;
int flag_branchDRF1;

//program counters for each stage
int pc_commit=-1;
int pc_wb=-1;

int pc_memory3=-1;
int pc_memory2=-1;
int pc_memory1=-1;

int pc_mul4=-1;
int pc_mul3=-1;
int pc_mul2=-1;
int pc_mul1=-1;

int pc_int=-1;

int pc_execute=-1;
int pc_decode2=-1;
int pc_decode1=-1;
int pc_fetch2=-1;
int pc_fetch1=-1;

//instructions types
enum operation{
	ADD,
	SUB,
	MOVC,
    MOV,
	MUL,
	AND,
	OR,
	EX_OR,
	LOAD,
	STORE,
	BZ,
	BNZ,
	JUMP,
	BAL,
	HALT,
};

char *operate[]={"ADD","SUB","MOVC","MOV","MUL","AND","OR","EX-OR","LOAD","STORE","BZ","BNZ","JUMP","BAL","HALT"};


//data structure of an instruction
struct instru_info{
	enum operation op_code;
	int arg1;
	int arg1_addr;  //will hold PRF address
	int arf_addr;   //to update R in end
	int arg1_valid_bit;
	int arg2;
	int arg2_addr;
	int arg2_valid_bit;
	int arg3;
	int arg3_addr;
	int arg3_valid_bit;
	int pc;
};

//instruction in each stage
struct instru_info *fetch1_instru=NULL, *fetch2_instru=NULL,
                    *decode1_instru=NULL, *decode2_instru=NULL,
                    *execute_instru=NULL,
                    *IQhead_INT_instru=NULL,
                    *IQhead_MUL_instru=NULL,
                    *LSQhead_instru=NULL,
                    *int_instru=NULL,
                    *mul1_instru=NULL,
                    *mul2_instru=NULL,
                    *mul3_instru=NULL,
                    *mul4_instru=NULL,
                    *memory1_instru=NULL,
                    *memory2_instru=NULL,
                    *memory3_instru=NULL,
                    *wb_instru=NULL,
                    *commit_instru=NULL
                    ;

//Inst queue array
struct instru_info *IQ[8];

//LSQ
struct instru_info *LSQ[4];

//ROB
struct instru_info *ROB[16];


//roll back if branch
void func_rollback(){

    printf("\nRollback called.\n");
    int ROBindex=0,temp_prf=-1,i, IQindex=0, LSQindex=0;

    printf("\nRollback before ROB.\n");

    for(ROBindex=0;ROBindex<16;ROBindex++)
    {
        if(ROB[ROBindex]==int_instru)
            break;
    }
    //except branch itself
    ROBindex++;
    printf("\nRollback:branch at:%d.\n",ROBindex);
    for(;ROBindex<16;ROBindex++)
    {
        printf("\nRollback:check for rob entry.\n");
        if(ROB[ROBindex]==NULL)
        {
            printf("\nRoll back: checkpoint.\n");
            break;
        }
        /*
        AL clear
        free list
        rename table clear
        PRF_status clear
        */
        if(ROB[ROBindex]->op_code<9)
        {
            printf("\nRollback:reseting renaming structures.\n");
            temp_prf=ROB[ROBindex]->arg1_addr;
            PRF_status[temp_prf]=0;
            AL[temp_prf]=0;
            rename_table[ROB[ROBindex]->arf_addr]=-1;
            for(i=0;i<16;i++)
            {
                if(free_list[i]==-1)
                {
                    free_list[i]=temp_prf;
                    break;
                }
            }
        }

        printf("\nRollback:clear IQ.\n");
        for(IQindex=0;IQindex<8;IQindex++)
        {
            if(IQ[IQindex]==ROB[ROBindex])
            {
                IQ[IQindex]=NULL;
            }
        }

        printf("\nRollback:clear LSQ.\n");
        for(LSQindex=0;LSQindex<4;LSQindex++)
        {
            if(LSQ[LSQindex]==ROB[ROBindex])
            {
                LSQ[LSQindex]=NULL;
            }
        }

        printf("\nRollback:Set NULL.\n");
        if(wb_instru==ROB[ROBindex])
            wb_instru=NULL;

        if(memory1_instru==ROB[ROBindex])
            memory1_instru=NULL;

        if(memory2_instru==ROB[ROBindex])
            memory2_instru=NULL;

        if(memory3_instru==ROB[ROBindex])
            memory3_instru=NULL;


        if(mul1_instru==ROB[ROBindex])
            mul1_instru=NULL;


        if(mul2_instru==ROB[ROBindex])
            mul2_instru=NULL;


        if(mul3_instru==ROB[ROBindex])
            mul3_instru=NULL;


        if(mul4_instru==ROB[ROBindex])
            mul4_instru=NULL;

        ROB[ROBindex]=NULL;
    }

    printf("\nRollback: ROB checking complete.\n");
    if(decode1_instru!=NULL && decode1_instru->op_code<9)
    {
        printf("\nRollback:reseting renaming structures for decode 1.\n");
        temp_prf=decode1_instru->arg1_addr;
        PRF_status[temp_prf]=0;
        AL[temp_prf]=0;
        rename_table[decode1_instru->arf_addr]=-1;
        for(i=0;i<16;i++)
        {
            if(free_list[i]==-1)
            {
                free_list[i]=temp_prf;
                break;
            }
        }
    }
    decode1_instru=NULL;

    if(decode2_instru!=NULL && decode2_instru->op_code<9)
    {
        printf("\nRollback:reseting renaming structures for decode 2.\n");
        temp_prf=decode2_instru->arg1_addr;
        PRF_status[temp_prf]=0;
        AL[temp_prf]=0;
        rename_table[decode2_instru->arf_addr]=-1;
        for(i=0;i<16;i++)
        {
            if(free_list[i]==-1)
            {
                free_list[i]=temp_prf;
                break;
            }
        }
    }
    decode1_instru=NULL;
    fetch1_instru=NULL;
    fetch2_instru=NULL;

    printf("\nRollback done complete.\n");
    //done rolling back
}

//free pointers at exit
void func_exit(){
	free(fetch1_instru);
	fetch1_instru=NULL;
	free(fetch2_instru);
	fetch2_instru=NULL;
	free(decode1_instru);
	decode1_instru=NULL;
	free(decode2_instru);
	decode2_instru=NULL;
	free(execute_instru);
	execute_instru=NULL;

	free(IQhead_INT_instru);
	IQhead_INT_instru=NULL;
	free(IQhead_MUL_instru);
	IQhead_INT_instru=NULL;

    free(LSQhead_instru);
    LSQhead_instru=NULL;

    free(int_instru);
    int_instru=NULL;

    free(mul1_instru);
    mul1_instru=NULL;
    free(mul2_instru);
    mul2_instru=NULL;
    free(mul2_instru);
    mul2_instru=NULL;
    free(mul3_instru);
    mul3_instru=NULL;
    free(mul4_instru);
    mul4_instru=NULL;

    free(memory1_instru);
    memory1_instru=NULL;
    free(memory2_instru);
    memory2_instru=NULL;
    free(memory3_instru);
    memory3_instru=NULL;

	free(wb_instru);
	wb_instru=NULL;
	free(commit_instru);
	commit_instru=NULL;

	//free IQ pointers
	int i=0;
	for(i=0;i<8;i++)
    {
        free(IQ[i]);
        IQ[i]=NULL;
    }

	//free LSQ pointers
	for(i=0;i<4;i++)
    {
        free(LSQ[i]);
        LSQ[i]=NULL;
    }

    for(i=0;i<16;i++)
    {
        free(ROB[i]);
        ROB[i]=NULL;
    }

}

//functions for each instruction operation
int func_add(int reg1,int reg2){
	return (reg1+reg2);
}

int func_sub(int reg1,int reg2){
	return (reg1-reg2);
}

int func_mul(int reg1,int reg2){
	return (reg1*reg2);
}

int func_and(int reg1,int reg2){
	return (reg1 & reg2);
}

int func_or(int reg1,int reg2){
	return (reg1 | reg2);
}

int func_exor(int reg1,int reg2){
	return (reg1 ^ reg2);
}

int func_load(int reg,int lit){
	return (reg+lit);
}

int func_store(int reg,int lit){
	return (reg+lit);
}

void func_bz(int lit){
	pc_update=int_instru->pc+lit-20000;
}

void func_bnz(int lit){
	pc_update=int_instru->pc+lit-20000;
}

void func_jump(int reg,int lit){
	pc_update=(reg+lit-20000);
}

void func_bal(int reg,int lit){
	pc_update=(reg+lit-20000);
	PRF[int_instru->arg1_addr]=int_instru->arg1;
}

//func to extract inst opcode & args in D/RF 1
int extract_inst(){
        int d1_pc=decode1_instru->pc-20000;

        printf("\nPC decode stage 1: %d Instruction: %s",d1_pc,instruction[d1_pc]);

        //get instruction op code
        char *token,temp_inst[20];
        strcpy(temp_inst,instruction[d1_pc]);
        token=strtok(temp_inst," ,\n");
        int i=0;
        for(i=0;i<15;i++)        {
            if(strcmp(token, operate[i])==0)
                break;
        }
        decode1_instru->op_code=i;

        //destination register
        if(i<10)
        {
            token=strtok(NULL," ,\n");

            if(token==NULL)
            {
                decode1_instru->arg1_addr=-1;
                decode1_instru->arg1=0;
                decode1_instru->arg1_valid_bit=0;
            }
            else if(token[0]=='R')
            {
                decode1_instru->arg1_addr=token[1]-'0';
                decode1_instru->arg1=R[decode1_instru->arg1_addr];
            }
            else if(token[0]=='X')
            {
                decode1_instru->arg1=X;
                decode1_instru->arg1_addr=8;
            }
            else
            {
                decode1_instru->arg1_addr=-1;
                decode1_instru->arg1=atoi(token);
                decode1_instru->arg1_valid_bit=0;
            }
        }
        else
        {
            decode1_instru->arg1_addr=-1;
            decode1_instru->arg1=0;
            decode1_instru->arg1_valid_bit=0;

        }

        //to update R[] in write back save address
        decode1_instru->arf_addr=decode1_instru->arg1_addr;

        //read argument 2
        token=strtok(NULL," ,\n");

        if(token==NULL)
        {
            decode1_instru->arg2_addr=-1;
            decode1_instru->arg2=0;
            decode1_instru->arg2_valid_bit=0;
        }
        else if(token[0]=='R')
        {
            decode1_instru->arg2_addr=token[1]-'0';
            decode1_instru->arg2=R[decode1_instru->arg2_addr];
        }
        else if(token[0]=='X')
        {
            decode1_instru->arg2=X;
            decode1_instru->arg2_addr=8;
        }
        else
        {
            decode1_instru->arg2_addr=-1;
            decode1_instru->arg2=atoi(token);
            decode1_instru->arg2_valid_bit=0;
        }

        //read argument 3
        token=strtok(NULL," \n");

        if(token==NULL)
        {
            decode1_instru->arg3_addr=-1;
            decode1_instru->arg3=0;
            decode1_instru->arg3_valid_bit=0;
        }
        else if(token[0]=='R')
        {
            decode1_instru->arg3_addr=token[1]-'0';
            decode1_instru->arg3=R[decode1_instru->arg3_addr];
        }
        else if(token[0]=='X')
        {
            decode1_instru->arg3=X;
            decode1_instru->arg3_addr=8;
        }
        else
        {
            decode1_instru->arg3_addr=-1;
            decode1_instru->arg3=atoi(token);
            decode1_instru->arg3_valid_bit=0;
        }


        if(decode1_instru->op_code==13)
        {
            decode1_instru->arg1_addr=8;
            decode1_instru->arf_addr=8;

            if(fetch1_instru!=NULL)
                decode1_instru->arg1=fetch1_instru->pc;
        }

    return d1_pc;
}

//initialize menu choice
void initialize(){
	int i=0;

	no_of_instru=0;

	//initializing flags
	flag_zero=0;
	flag_halt=0;
	flag_done=0;

	dependent_flag = 0;
	dependent_reg = -1;

	flag_IQfull=0;
	flag_LSQfull=0;
	flag_freeList=0;
	flag_ROBfull=0;

    flag_INTstall=0;
    flag_MULstall=0;
    flag_MULoccupied=0;
    flag_predtaken=0;
    flag_branchDRF1=0;

    execute_intpc=-1;
    execute_mul1pc=-1;
    execute_memory1pc=-1;

	//initializing program counters
	pc_update=INT_MAX;
	current_pc = 0;

    //total cycles done
    cycles_done=0;

    //initializing registers
	for(i=0;i<8;i++)
	{
		R[i]=0;
	}
	X=0;

	for(i=0;i<9;i++)
	{
	    //initializing register status bits 0 - valid
		reg_status[i]=0;

		//rename table initialize
		rename_table[i] = -1;
	}

    for(i=0;i<16;i++)
    {
        //physical registers
        // 0 - valid
        PRF[i]=0;
        PRF_status[i]=0; //invalid status

        //renaming initializing
        free_list[i]=i;
        AL[i]=0; //not allocated
        renamed_array[i]=0; //not renamed

        ROB[i]=NULL;
    }

	//initializing memory
	for(i=0;i<10000;i++)
	{
		mem[i]=0;
	}

	//initializing IQ array
	for(i=0;i<8;i++)
    {
        IQ[i]=NULL;
    }

    //initializing LSQ array
    for(i=0;i<4;i++)
    {
        LSQ[i]=NULL;
    }

    //open file to read
	FILE *fptr=fopen(filename,"r");

	//check if able to open file
	if(fptr==NULL)
	{
		printf("\nFile not found.\n");
		exit(-1);
	}

	char temp[20];

	while(!feof(fptr))
	{
		while(fgets(temp,20,fptr)!=NULL)
		{
			strcpy(instruction[no_of_instru++],temp);
			printf("%s",instruction[no_of_instru-1]);
		}
	}
	printf("\n\nNumber of instructions read: %d\n\n",no_of_instru);

	decode1_instru=NULL;
	decode2_instru=NULL;
	execute_instru=NULL;

	IQhead_INT_instru=NULL;
	IQhead_MUL_instru=NULL;
	LSQhead_instru=NULL;

    int_instru=NULL;

    mul1_instru=NULL;
    mul2_instru=NULL;
    mul3_instru=NULL;
    mul4_instru=NULL;

    memory1_instru=NULL;
    memory2_instru=NULL;
    memory3_instru=NULL;

	wb_instru=NULL;
	fetch2_instru=NULL;
	fetch1_instru=NULL;
	pc_offset=20000;

    //reset program counters
    pc_fetch1 = -1;
	pc_fetch2 = -1;
	pc_decode2 = -1;
	pc_decode1 = -1;
	pc_execute = -1;

	pc_int = -1;

	pc_memory1 = -1;
	pc_memory2 = -1;
	pc_memory3 = -1;

	pc_mul1 = -1;
	pc_mul2 = -1;
	pc_mul3 = -1;
	pc_mul4 = -1;

	pc_wb = -1;
	pc_commit = -1;

	return;
}

//FETCH stage 1
int fetch_stage1(){

    //halt
    if(flag_halt==1)
    {
        printf("\nHalt encountered fetch 2 stage.\n\n");
        fetch1_instru=NULL;
        return -1;
    }

    //printf("fetch stage 1 before dependent flag 1 check.\n");
    if(dependent_flag==1)
    {
        printf("\nSTALL in fetch stage 1\n\n");
		//return fetch1_instru->pc-20000;
        return -1;
    }

    //printf("fetch stage 1 after dependent flag 1 check.\n");
    if(flag_IQfull==1)
    {
        printf("STALL in fetch 1 due to IQ full.\n");
        return -1;
    }

    if(flag_ROBfull==1)
    {
        printf("STALL in fetch 1 due to ROB full.\n");
        return -1;
    }

    //printf("fetch stage 1 before flag freelist 1 check.\n");

    if(flag_freeList==1)
    {
        printf("STALL in fetch 1 due to no free physical reg in free list.\n");
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("\nPC fetch stage 1= %d Instruction= %s\n",current_pc,instruction[current_pc]);
        fetch1_instru=(struct instru_info*)malloc(sizeof(struct instru_info));

        if((int_instru->op_code==10) || (int_instru->op_code==11))
        {
            current_pc=pc_update;    // bcoz out of order execution
        }
        else if ((int_instru->op_code==12) || (int_instru->op_code==13))
        {
            current_pc=pc_update;
        }
        //ankush branch pred
        if (flag_branchDRF1==1 &&(decode1_instru->op_code==10 || decode1_instru->op_code==11))
        {
            current_pc=pc_update;
            flag_branchDRF1=0;
        }

        fetch1_instru->pc=current_pc+20000;
        pc_update=INT_MAX;
        fetch1_instru=NULL;

        if(current_pc==no_of_instru)
        {
            flag_done=1;
        }

        return -1;
    }

    //printf("fetch stage 1 current_pc>=no_of_instru check.\n");

    if(flag_predtaken==1)
    {
        printf("\nSTALL in fetch stage 1 due to branch prediction of taken.\n");
        return -1;
    }

    //no more instructions to fetch
    if(current_pc>=no_of_instru)
    {
        printf("\nNo instructions to fetch in stage 1.\n");
        fetch1_instru = NULL;
        return -1;
    }

    //printf("fetch stage 1 dependent_flag 0 check\n");
    //get next instruction
    if(dependent_flag==0)
    {
        printf("\nPC fetch stage 1: %d Instruction: %s\n",current_pc,instruction[current_pc]);
        fetch1_instru=(struct instru_info*)malloc(sizeof(struct instru_info));
        fetch1_instru->pc=current_pc+20000;
        current_pc++;
        if((current_pc-1)==no_of_instru)
        {
            flag_done=1;
        }
        return fetch1_instru->pc-20000;
    }

    //printf("fetch stage 1 last.\n");
}

//FETCH stage 2
int fetch_stage2(){

    //halt
    if(flag_halt==1)
    {
        printf("\nHalt encountered fetch 2 stage.\n\n");
        fetch2_instru=NULL;
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("\nSTALL due to branch fetch 2 stage.\n\n");
        fetch2_instru=NULL;
        return -1;
    }

    if(flag_predtaken==1)
    {
        printf("\nSTALL due to branch prediction of taken.\n");
        fetch2_instru=NULL;
        return -1;
    }

    //stall
    if(dependent_flag==1)
    {
        printf("\nSTALL in fetch 2 stage.\n\n");
        return -1;
        //return fetch2_instru->pc-20000;
    }

    if(flag_IQfull==1)
    {
        printf("STALL in fetch 2 due to IQ full.\n");
        return -1;
    }

    if(flag_ROBfull==1)
    {
        printf("STALL in fetch 2 due to ROB full.\n");
        return -1;
    }

    if(flag_freeList==1)
    {
        printf("STALL in fetch 2 due to no free physical reg in free list.\n");
        return -1;
    }
    //No instructions to get from fetch 1 stage
    if(fetch1_instru==NULL)
    {
        printf("\nNo instructions in fetch 2 stage.\n\n");
        fetch2_instru=NULL;
        return -1;
    }

    //get next intruction from fetch stage 1 to 2
    if(dependent_flag==0)
    {
        fetch2_instru=fetch1_instru;
        int fetch2_pc=fetch2_instru->pc-20000;
        printf("\nPC fetch stage 2: %d  Instruction: %s\n",fetch2_pc,instruction[fetch2_pc]);
        return fetch2_pc;
    }
}

//D/RF 1
int decode_stage1(){
    //halt
    if(flag_halt==1)
    {
        printf("\nHalt encountered fetch 2 stage.\n\n");
        decode1_instru=NULL;
        return -1;
    }
    //in case of branch
    if(pc_update!=INT_MAX)
    {
        printf("\nSTALL due to branch decode stage 1.\n\n");
        decode1_instru=NULL;
        return -1;
    }

    //in case of stall in case of dependency
    if(dependent_flag==1)
    {
        printf("\nSTALL in decode stage 1\n\n");
        return -1;
        //return decode1_instru->pc-20000;
    }

    // no instruction to get from fetch 2
    if(fetch2_instru==NULL)
    {
        printf("\nNo instructions to decode stage 1.\n\n");
        decode1_instru=NULL;
        return -1;
    }

    //process next incoming instruction
    if(dependent_flag==0)
    {
        decode1_instru=fetch2_instru;
        int decode1_pc = -1;
        int IQindex,ROBindex,LSQindex;

        for(ROBindex=0;ROBindex<16;ROBindex++)
        {
            if(ROB[ROBindex]==NULL)
                break;
        }
        if(ROBindex==16)
        {
            flag_ROBfull=1;
            printf("\nSTALL in Decode stage 1 due to ROB full.\n");
            return -1;
        }
        else
        {
            flag_ROBfull=0;

            //call to func to extract opcode & args from inst
            decode1_pc=extract_inst();

            if(decode1_instru->op_code<8 ||decode1_instru->op_code>9)
            {

                for(IQindex=0;IQindex<8;IQindex++)
                {
                    if (IQ[IQindex]==NULL)
                        break;
                }

                if(IQindex==8)
                {
                    //STALL instructions due to IQ full
                    flag_IQfull=1;
                    printf("\nSTALL in Decode stage 1 due to IQ full.\n");
                    return -1;
                }
            }
            flag_IQfull=0;

            if(decode1_instru->op_code==8 ||decode1_instru->op_code==9)
            {
                for(LSQindex=0;LSQindex<4;LSQindex++)
                {
                    if (LSQ[LSQindex]==NULL)
                        break;
                }

                if(LSQindex==8)
                {
                    //STALL instructions due to IQ full
                    flag_LSQfull=1;
                    printf("\nSTALL in Decode stage 1 due to LSQ full.\n");
                    return -1;
                }
            }
            flag_LSQfull=0;

        }
        if(decode1_instru->op_code==10 || decode1_instru->op_code==11)
        {
            decode1_instru->arg1_addr=decode2_instru->arg1_addr;

            if(decode1_instru->arg2<0)
            {
                flag_predtaken=1;
                flag_branchDRF1=1;
                pc_update=decode1_instru->pc+decode1_instru->arg2-20000;
            }
        }

        //printf("   Decode:  %d:%d:%d:%d:%d:%d:%d:%d\n\n",decode1_instru->op_code,decode1_instru->arg1,decode1_instru->arg1_addr,decode1_instru->arg2,decode1_instru->arg2_addr,decode1_instru->arg3,decode1_instru->arg3_addr,decode1_instru->pc);

        if(decode1_instru->op_code==14)
        {
            flag_halt=1;
        }
        return decode1_pc;
    }


}

//D/RF 2
int decode_stage2(){

    flag_predtaken=0;

    if(pc_update!=INT_MAX)
    {
        printf("\nSTALL due to branch decode stage 2.\n\n");
        decode2_instru=NULL;
        return -1;
    }

    if(dependent_flag==1)
    {
        printf("\nSTALL in decode stage 2\n\n");
        /*  to copy latest value of dependent register from write back so that updated
        value is passed to execute in next cycle when dependency is removed via commit stage. */
        if(decode2_instru->op_code==9)
        {
            if(decode2_instru->arg1_addr==dependent_reg && decode2_instru->arg1_valid_bit==1)
            {
                decode2_instru->arg1=PRF[decode2_instru->arg1_addr];
                decode2_instru->arg1_valid_bit=PRF_status[decode2_instru->arg1_addr];
            }
        }

        //BZ / BNZ internal reg for introducing dependency
        if(decode2_instru->op_code==10 ||decode2_instru->op_code==11)
        {
            if(decode2_instru->arg1_addr==dependent_reg && decode2_instru->arg1_valid_bit==1)
            {
                decode2_instru->arg1=PRF[decode2_instru->arg1_addr];
                decode2_instru->arg1_valid_bit=PRF_status[decode2_instru->arg1_addr];
            }
        }

        if(decode2_instru->arg2_addr==dependent_reg && decode2_instru->arg2_valid_bit==1)
        {
            decode2_instru->arg2=PRF[decode2_instru->arg2_addr];
            decode2_instru->arg2_valid_bit=PRF_status[decode2_instru->arg2_addr];
        }
        if(decode2_instru->arg3_addr==dependent_reg && decode2_instru->arg3_valid_bit==1)
        {
            decode2_instru->arg3=PRF[decode2_instru->arg3_addr];
            decode2_instru->arg3_valid_bit=PRF_status[decode2_instru->arg3_addr];

        }
        return -1;
    }

    if(decode1_instru==NULL)
    {
        printf("\nNo instructions to decode in stage 2.\n\n");
        decode2_instru=NULL;
        return -1;
    }



    if(dependent_flag==0)
    {
        decode2_instru=decode1_instru;
        int decode2_pc=decode2_instru->pc-20000;

        printf("\nPC decode stage 2: %d Instruction: %s",decode2_pc,instruction[decode2_pc]);

        //for source registers
        //arg1 for STORE
        if(decode2_instru->op_code==9)
        {
            if(decode2_instru->arg1_addr!=-1)
            {
                if(rename_table[decode2_instru->arg1_addr]!=-1)
                {
                    decode2_instru->arg1_addr=rename_table[decode2_instru->arg1_addr];
                    decode2_instru->arg1=PRF[decode2_instru->arg1_addr];
                    decode2_instru->arg1_valid_bit=PRF_status[decode2_instru->arg1_addr];
                }
                else
                {
                    decode2_instru->arg1=R[decode2_instru->arg1_addr];
                    decode2_instru->arg1_addr=-1;
                    decode2_instru->arg1_valid_bit=0;
                }
            }
        }

        if(decode2_instru->arg2_addr!=-1)  //not lit & exists
        {
            if(rename_table[decode2_instru->arg2_addr]!=-1)
            {
                decode2_instru->arg2_addr=rename_table[decode2_instru->arg2_addr];
                decode2_instru->arg2=PRF[decode2_instru->arg2_addr];
                decode2_instru->arg2_valid_bit=PRF_status[decode2_instru->arg2_addr];

            }
                else
                {
                    decode2_instru->arg2=R[decode2_instru->arg2_addr];
                    decode2_instru->arg2_addr=-1;
                    decode2_instru->arg2_valid_bit=0;
                }
        }

        if(decode2_instru->arg3_addr!=-1)
        {
            if(rename_table[decode2_instru->arg3_addr]!=-1)
            {
                decode2_instru->arg3_addr=rename_table[decode2_instru->arg3_addr];
                decode2_instru->arg3=PRF[decode2_instru->arg3_addr];
                decode2_instru->arg3_valid_bit=PRF_status[decode2_instru->arg3_addr];
            }
                else
                {
                    decode2_instru->arg3=R[decode2_instru->arg3_addr];
                    decode2_instru->arg3_addr=-1;
                    decode2_instru->arg3_valid_bit=0;
                }
        }


        //BZ / BNZ internal reg for introducing dependency
        if(decode2_instru->op_code==10 ||decode2_instru->op_code==11)
        {
            //if(rename_table[decode2_instru->arg1_addr]!=-1)
            {
                //decode2_instru->arg1_addr=rename_table[decode2_instru->arg1_addr];
                decode2_instru->arg1=PRF[decode2_instru->arg1_addr];
                decode2_instru->arg1_valid_bit=PRF_status[decode2_instru->arg1_addr];
            }
        }






        //copied for decode1 till ROB
        //for dest reg assign physical reg
        if(decode2_instru->op_code<9 || decode2_instru->op_code==13)
        {
            //no physical reg in free list
            if(free_list[0]==-1)
            {
                flag_freeList=1;
                printf("STALL in decode stage 2 due to no physical reg in free list.\n");
                return -1;
            }
            else
            {
                //do everything to assign physical register to destination
                //update rename table, renamed array, AL, PRF_status, free list
                if(rename_table[decode2_instru->arg1_addr]!=-1)
                {
                    renamed_array[rename_table[decode2_instru->arg1_addr]]=1; //previous phy reg renamed
                    AL[rename_table[decode2_instru->arg1_addr]]=0; //previous physical reg

                    /*put in free list when deallocated (when renamed and status bit valid
                        = when architectural reg written with that physical reg value). */
                }

                AL[free_list[0]]=1; //mark allocated
                PRF_status[free_list[0]]=1;  //mark invalid
                rename_table[decode2_instru->arg1_addr]=free_list[0];

                decode2_instru->arg1_addr=free_list[0];

                //shift free_list values and add -1 at end**** to handle it
                int j;
                for(j=0;j<16;j++)
                {
                    free_list[j] = free_list[j+1];
                }
                free_list[15] = -1;
            }
        }

        //put instru in ROB
        int ROBindex,IQindex,LSQindex;

        for(ROBindex=0;ROBindex<16;ROBindex++)
        {
            if(ROB[ROBindex]==NULL)
            {
                ROB[ROBindex]=decode2_instru;
                break;
            }
        }

        // put instruction in IQ and LSQ
        if(decode2_instru->op_code<8 || decode2_instru->op_code>9)
        {

            for(IQindex=0;IQindex<8;IQindex++)
            {
                if(IQ[IQindex]==NULL)
                {
                    IQ[IQindex]=decode2_instru;
                    break;
                }
            }

            if((IQ[IQindex]->op_code==10 || IQ[IQindex]->op_code==11) && IQ[IQindex]->arg1_valid_bit==1)
            {
                IQ[IQindex]->arg1=PRF[IQ[IQindex]->arg1_addr];
                IQ[IQindex]->arg1_valid_bit=PRF_status[IQ[IQindex]->arg1_addr];
            }
            if(IQ[IQindex]->arg2_valid_bit==1)
            {
                IQ[IQindex]->arg2=PRF[IQ[IQindex]->arg2_addr];
                IQ[IQindex]->arg2_valid_bit=PRF_status[IQ[IQindex]->arg2_addr];
            }
            if(IQ[IQindex]->arg3_valid_bit==1)
            {
                IQ[IQindex]->arg3=PRF[IQ[IQindex]->arg3_addr];
                IQ[IQindex]->arg3_valid_bit=PRF_status[IQ[IQindex]->arg3_addr];
            }
        }
        else
        {
            for(LSQindex=0;LSQindex<4;LSQindex++)
            {
                if(LSQ[LSQindex]==NULL)
                {
                    LSQ[LSQindex]=decode2_instru;
                    break;
                }
            }

            if(LSQ[LSQindex]->op_code==9 && LSQ[LSQindex]->arg1_valid_bit==1)
            {
                LSQ[LSQindex]->arg1=PRF[LSQ[LSQindex]->arg1_addr];
                LSQ[LSQindex]->arg1_valid_bit=PRF_status[LSQ[LSQindex]->arg1_addr];
            }

            if(LSQ[LSQindex]->arg2_valid_bit==1)
            {
                LSQ[LSQindex]->arg2=PRF[LSQ[LSQindex]->arg2_addr];
                LSQ[LSQindex]->arg2_valid_bit=PRF_status[LSQ[LSQindex]->arg2_addr];
            }

            if(LSQ[LSQindex]->arg3_valid_bit==1)
            {
                LSQ[LSQindex]->arg3=PRF[LSQ[LSQindex]->arg3_addr];
                LSQ[LSQindex]->arg3_valid_bit=PRF_status[LSQ[LSQindex]->arg3_addr];
            }
        }
        //printf("   Decode 2:  %d:%d:%d:%d:%d:%d:%d:%d\n\n",decode2_instru->op_code,decode2_instru->arg1,decode2_instru->arg1_addr,decode2_instru->arg2,decode2_instru->arg2_addr,decode2_instru->arg3,decode2_instru->arg3_addr,decode2_instru->pc);
        return decode2_pc;
    }
}


void data_forwarding(){
    IQ_handling();
    LSQ_handling();
}

void IQ_handling(){

    int IQindex;
    for(IQindex=0;IQindex<8;IQindex++)
    {

        if(IQ[IQindex]!=NULL)
        {

        //check physical reg status (for data forwarding)

            if(IQ[IQindex]->arg2_valid_bit==1 && IQ[IQindex]->arg2_addr!=-1)
            {
                IQ[IQindex]->arg2=PRF[IQ[IQindex]->arg2_addr];
                IQ[IQindex]->arg2_valid_bit=PRF_status[IQ[IQindex]->arg2_addr];

            }
            if(IQ[IQindex]->arg3_valid_bit==1 && IQ[IQindex]->arg3_addr!=-1)
            {
                IQ[IQindex]->arg3=PRF[IQ[IQindex]->arg3_addr];
                IQ[IQindex]->arg3_valid_bit=PRF_status[IQ[IQindex]->arg3_addr];
            }

            //BZ / BNZ internal reg for introducing dependency
            if((IQ[IQindex]->op_code==10 ||IQ[IQindex]->op_code==11) && IQ[IQindex]->arg1_valid_bit==1 && IQ[IQindex]->arg1_addr!=-1)
            {
                    IQ[IQindex]->arg1=PRF[IQ[IQindex]->arg1_addr];
                    IQ[IQindex]->arg1_valid_bit=PRF_status[IQ[IQindex]->arg1_addr];
            }
        }
    }
}

void LSQ_handling(){

    int LSQindex;
    for(LSQindex=0;LSQindex<4;LSQindex++)
    {

        if(LSQ[LSQindex]!=NULL)
        {

        //check physical reg status (for data forwarding)
            if(LSQ[LSQindex]->op_code==9 && LSQ[LSQindex]->arg1_valid_bit==1 && LSQ[LSQindex]->arg1_addr!=-1)
            {
                LSQ[LSQindex]->arg1=PRF[LSQ[LSQindex]->arg1_addr];
                LSQ[LSQindex]->arg1_valid_bit=PRF_status[LSQ[LSQindex]->arg1_addr];

            }
            if(LSQ[LSQindex]->arg2_valid_bit==1 && LSQ[LSQindex]->arg2_addr!=-1)
            {
                LSQ[LSQindex]->arg2=PRF[LSQ[LSQindex]->arg2_addr];
                LSQ[LSQindex]->arg2_valid_bit=PRF_status[LSQ[LSQindex]->arg2_addr];

            }
            if(LSQ[LSQindex]->arg3_valid_bit==1 && LSQ[LSQindex]->arg3_addr!=-1)
            {
                LSQ[LSQindex]->arg3=PRF[LSQ[LSQindex]->arg3_addr];
                LSQ[LSQindex]->arg3_valid_bit=PRF_status[LSQ[LSQindex]->arg3_addr];
            }
        }
    }
}

//main execute
int execute(){

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("STALL Due to branch  execute.\n\n");
        execute_instru=NULL;
        return -1;
    }

    //get instruction from IQ[0] rather than decode2_instru and remove that from IQ[0] and shift IQ
    //IQhead_instru=IQ[0];

    int IQindex_INT;
    int IQindex_MUL;
    int LSQindex;

    IQhead_INT_instru=NULL;
    IQhead_MUL_instru=NULL;
    LSQhead_instru=NULL;

    for(IQindex_MUL=0;IQindex_MUL<8;IQindex_MUL++)
    {
        if(IQ[IQindex_MUL]!=NULL)
        {
            if(IQ[IQindex_MUL]->arg2_valid_bit!=1 && IQ[IQindex_MUL]->arg3_valid_bit!=1 && IQ[IQindex_MUL]->op_code==4)
            {
                    IQhead_MUL_instru=IQ[IQindex_MUL];
                    break;
            }
        }
    }

    for(IQindex_INT=0;IQindex_INT<8;IQindex_INT++)
    {
        if(IQ[IQindex_INT]!=NULL)
        {
            if((IQ[IQindex_INT]->op_code==10 || IQ[IQindex_INT]->op_code==11) && IQ[IQindex_INT]->arg1_valid_bit!=1)
            {
                IQhead_INT_instru=IQ[IQindex_INT];
                break;
            }
            else if(IQ[IQindex_INT]->op_code!=4 && IQ[IQindex_INT]->arg2_valid_bit!=1 && IQ[IQindex_INT]->arg3_valid_bit!=1)
            {
                IQhead_INT_instru=IQ[IQindex_INT];
                break;
            }
        }
    }

    LSQindex=0;

    if(LSQ[LSQindex]!=NULL)
    {
        if(LSQ[LSQindex]->op_code==9)
        {
            if(LSQ[LSQindex]->arg1_valid_bit!=1 && LSQ[LSQindex]->arg2_valid_bit!=1 && LSQ[LSQindex]->arg3_valid_bit!=1)
            {
                LSQhead_instru=LSQ[LSQindex];
            }
        }
        else
        {
            if(LSQ[LSQindex]->arg2_valid_bit!=1 && LSQ[LSQindex]->arg3_valid_bit!=1)
            {
                LSQhead_instru=LSQ[LSQindex];
            }
        }
    }


    //no instruction to get from decode
    if(IQhead_INT_instru==NULL && IQhead_MUL_instru==NULL && LSQhead_instru==NULL)
    {
        printf("No instructions to execute.\n\n");
        execute_instru=NULL;
        return -1;
    }

    //STORE - stall due to argument 1 invalid
	if(LSQhead_instru!=NULL && LSQhead_instru->op_code==9)
	{
        if(LSQhead_instru!=ROB[0])
        {
            printf("\nMemory 1 : STORE is not at ROB head.\n");
            execute_instru=NULL;
            LSQhead_instru=NULL;
        }
	}

    int execute_pc=-1;

    if(LSQhead_instru!=NULL && (LSQhead_instru->op_code==8||LSQhead_instru->op_code==9))
    {
            execute_pc=execute_memory1();
            execute_memory1pc=execute_pc;
            execute_instru=memory1_instru;
    }

    if(flag_INTstall!=1 && IQhead_INT_instru!=NULL)
    {
        execute_pc=execute_int();
        execute_intpc=execute_pc;
        execute_instru=int_instru;
    }

    if(IQhead_MUL_instru!=NULL && flag_MULoccupied!=1)
    {
        execute_pc=execute_mul1();
        execute_mul1pc=execute_pc;
        execute_instru=mul1_instru;
        memory1_instru=NULL;
    }
/*
            else
            {
                printf("unknown instruction / STALL in execute.\n");
                execute_instru=NULL;
                return -1;
            }
*/

    return execute_pc;
}

//INT FU EXECUTE
int execute_int(){

    //no instruction to get from decode
    if(flag_INTstall==1)
    {
        printf("STALL in execute INT due to write back occupied by memory inst.\n");
        int_instru=NULL;
        return -1;
    }

    if(IQhead_INT_instru==NULL)
    {
        printf("No instructions to execute_int.\n\n");
        int_instru=NULL;
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("STALL Due to branch  execute_int.\n\n");
        int_instru=NULL;
        return -1;
    }

    //no stall
        if(dependent_flag!=1)
        {

            //process instruction from decode to execute_int stage
            int_instru=IQhead_INT_instru;
            int execute_int_pc=int_instru->pc-20000;


            //IQ shifting
            int IQ_index=0;
            for(IQ_index=0;IQ_index<7;IQ_index++)
            {
                if(IQ[IQ_index]==IQhead_INT_instru)
                    break;

            }
            for(;IQ_index<7;IQ_index++)
            {
                    IQ[IQ_index]=IQ[IQ_index+1];
            }
            IQ[7]=NULL;

            printf("\nPC execute_int:%d  Instruction: %s", execute_int_pc,instruction[execute_int_pc]);
            switch(int_instru->op_code)
            {
                //ADD inst
                case 0:
                    int_instru->arg1=func_add(int_instru->arg2,int_instru->arg3);
                    break;

                //SUB inst
                case 1:
                    int_instru->arg1=func_sub(int_instru->arg2,int_instru->arg3);
                    break;

                //MOVC inst
                case 2:
                    int_instru->arg1=int_instru->arg2;
                    break;

                //MOV inst
                case 3:
                    int_instru->arg1=int_instru->arg2;
                    break;

                //AND inst
                case 5:
                    int_instru->arg1=func_and(int_instru->arg2,int_instru->arg3);
                    break;

                //OR inst
                case 6:
                    int_instru->arg1=func_or(int_instru->arg2,int_instru->arg3);
                    break;

                //X-OR inst
                case 7:
                    int_instru->arg1=func_exor(int_instru->arg2,int_instru->arg3);
                    break;

                //BZ inst
                case 10:
                    if(int_instru->arg1==0)
                    {
                        printf("\nint_instru->arg1:%d\n",int_instru->arg1);
                        if(int_instru->arg2>0) //mis-prediction
                        {
                            func_bz(int_instru->arg2);
                            func_rollback();
                        }
                    }
                    else
                    {
                        if(int_instru->arg2<0)
                        {
                            func_rollback();
                            func_bz(1);
                        }
                    }
                    break;

                //BNZ inst
                case 11:
                    if(int_instru->arg1!=0)
                    {
                        printf("\nint_instru->arg1:%d\n",int_instru->arg1);
                        if(int_instru->arg2>0) //mis-prediction
                        {
                            func_bnz(int_instru->arg2);
                            func_rollback();
                        }
                    }
                    else
                    {
                        if(int_instru->arg2<0)
                        {
                            func_rollback();
                            func_bnz(1);
                        }
                    }
                    break;

                //JUMP inst
                case 12:
                    func_jump(int_instru->arg2,int_instru->arg3);
                    break;

                //BAL inst
                case 13:
                    func_bal(int_instru->arg2,int_instru->arg3);
                    break;

                //HALT inst
                case 14:
                    //halt  //from write back
                    break;
                //default / NOP
                default:
                    printf("Illegal token execute_int.\n");
            }

            //reset reg status of dest reg for insts till LOAD
            if(int_instru->op_code<9 )
            {
                PRF[int_instru->arg1_addr]=int_instru->arg1;
            }

            //printf("   Execute int: %d:%d:%d:%d:%d:%d:%d:%d\n\n",int_instru->op_code,int_instru->arg1,int_instru->arg1_addr,int_instru->arg2,int_instru->arg2_addr,int_instru->arg3,int_instru->arg3_addr,int_instru->pc);

			//branching with roll back
			if(int_instru->op_code==12 || int_instru->op_code==13)
                func_rollback();

			return execute_int_pc;
        }
        else
        {
            return -1;
        }

}

//MUL FU EXECUTE
int execute_mul1(){

    //MUL non pipelined - already instruction in MUL FU
    if(flag_MULoccupied==1)
    {
        printf("STALL in non-pipelined execute MUL 1 as already inst executing in MUL FU.\n");
//        mul1_instru=NULL;
        return -1;
    }

    //no instruction to get from IQ

    if(IQhead_MUL_instru==NULL)
    {
        printf("No instructions to execute_mul 1.\n\n");
        mul1_instru=NULL;
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("STALL Due to branch  execute_mul.\n\n");
        mul1_instru=NULL;
        return -1;
    }

//no stall
    if(dependent_flag!=1)
    {
        //process instruction from decode to execute_mul stage
        mul1_instru=IQhead_MUL_instru;
        int execute_mul1_pc=mul1_instru->pc-20000;

        //IQ shifting
        int IQ_index=0;
        for(IQ_index=0;IQ_index<7;IQ_index++)
        {
            if(IQ[IQ_index]==IQhead_MUL_instru)
                break;

        }
        for(;IQ_index<7;IQ_index++)
        {
                IQ[IQ_index]=IQ[IQ_index+1];
        }
        IQ[7]=NULL;

        printf("\nPC execute_mul 1:%d  Instruction: %s", execute_mul1_pc,instruction[execute_mul1_pc]);


        //printf("   Execute mul 1: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul1_instru->op_code,mul1_instru->arg1,mul1_instru->arg1_addr,mul1_instru->arg2,mul1_instru->arg2_addr,mul1_instru->arg3,mul1_instru->arg3_addr,mul1_instru->pc);
        return execute_mul1_pc;
    }
    else
    {
        return -1;
    }
}

//MUL FU EXECUTE
int execute_mul2(){
    //no instruction to get from mul 1

    if(mul1_instru==NULL)
    {
        printf("No instructions in execute mul 2 to get from execute_mul 1.\n\n");
        mul2_instru=NULL;
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("STALL Due to branch execute_mul 2.\n\n");
        mul2_instru=NULL;
        return -1;
    }

//no stall
    if(dependent_flag!=1)
    {
        //process instruction from decode to execute_mul stage
        mul2_instru=mul1_instru;
        //mul1_instru=NULL;
        int execute_mul2_pc=mul2_instru->pc-20000;

        printf("\nPC execute_mul 2:%d  Instruction: %s", execute_mul2_pc,instruction[execute_mul2_pc]);


        //printf("   Execute mul 2: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul2_instru->op_code,mul2_instru->arg1,mul2_instru->arg1_addr,mul2_instru->arg2,mul2_instru->arg2_addr,mul2_instru->arg3,mul2_instru->arg3_addr,mul2_instru->pc);
        return execute_mul2_pc;
    }
    else
    {
        return -1;
    }
}

//MUL FU EXECUTE
int execute_mul3(){
    //no instruction to get from mul 1

    if(mul2_instru==NULL)
    {
        printf("No instructions in execute mul 3 to get from execute_mul 2.\n\n");
        mul3_instru=NULL;
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("STALL Due to branch  execute_mul 3.\n\n");
        mul3_instru=NULL;
        return -1;
    }

//no stall
    if(dependent_flag!=1)
    {
        //process instruction from decode to execute_mul stage
        mul3_instru=mul2_instru;
        mul2_instru=NULL;

        int execute_mul3_pc=mul3_instru->pc-20000;

        printf("\nPC execute_mul 3:%d  Instruction: %s", execute_mul3_pc,instruction[execute_mul3_pc]);

        //printf("   Execute mul 3: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul3_instru->op_code,mul3_instru->arg1,mul3_instru->arg1_addr,mul3_instru->arg2,mul3_instru->arg2_addr,mul3_instru->arg3,mul3_instru->arg3_addr,mul3_instru->pc);
        return execute_mul3_pc;
    }
    else
    {
        return -1;
    }
}

//MUL FU EXECUTE
int execute_mul4(){

    //no instruction to get from mul 3

    if(mul3_instru==NULL)
    {
        printf("No instructions to execute_mul 4.\n\n");
        mul4_instru=NULL;
        return -1;
    }

    if(flag_MULstall==1)
    {
        printf("STALL in execute MUL 4 due to write back occupied.\n");
        mul4_instru=mul3_instru;
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("STALL Due to branch  execute_mul 4.\n\n");
        mul4_instru=NULL;
        return -1;
    }

//no stall
    if(dependent_flag!=1)
    {
        //process instruction from decode to execute_mul stage
        mul4_instru=mul3_instru;
        int execute_mul4_pc=mul4_instru->pc-20000;

        printf("\nPC execute_mul 4:%d  Instruction: %s", execute_mul4_pc,instruction[execute_mul4_pc]);

        mul4_instru->arg1=func_mul(mul4_instru->arg2,mul4_instru->arg3);

        //reset reg status of dest reg for insts till LOAD
        PRF[mul4_instru->arg1_addr]=mul4_instru->arg1;

        printf("   Execute mul 4: %d:%d:%d:%d:%d:%d:%d:%d\n\n",mul4_instru->op_code,mul4_instru->arg1,mul4_instru->arg1_addr,mul4_instru->arg2,mul4_instru->arg2_addr,mul4_instru->arg3,mul4_instru->arg3_addr,mul4_instru->pc);
        return execute_mul4_pc;
    }
    else
    {
        return -1;
    }
 }

//MEMORY FU 1 EXECUTE
int execute_memory1(){
    //no instruction to get from decode
    if(LSQhead_instru==NULL)
    {
        printf("No instructions to execute_memory.\n\n");
        memory1_instru=NULL;
        return -1;
    }

    //branching
    if(pc_update!=INT_MAX)
    {
        printf("STALL Due to branch  execute_memory.\n\n");
        memory1_instru=NULL;
        return -1;
    }

    //no stall
    if(dependent_flag!=1)
    {
        //process instruction from decode to execute_memory stage
        memory1_instru=LSQhead_instru;
        int execute_memory1_pc=memory1_instru->pc-20000;

        //LSQ shifting
        int LSQ_index;
        for(LSQ_index=0;LSQ_index<3;LSQ_index++)
        {
            LSQ[LSQ_index]=LSQ[LSQ_index+1];
        }
        LSQ[4]=NULL;

        printf("\nPC execute_memory 1:%d  Instruction: %s", execute_memory1_pc,instruction[execute_memory1_pc]);
        switch(memory1_instru->op_code)
        {
            //LOAD inst
            case 8:
                memory1_instru->arg1=func_load(memory1_instru->arg2,memory1_instru->arg3);
                break;

            //STORE inst
            case 9:
                memory1_instru->arg1=func_store(memory1_instru->arg2,memory1_instru->arg3);
                break;

            default:
                printf("Illegal token execute_memory 1.\n");
        }

        //LOAD
        if(memory1_instru->op_code==8)
        {
            //sanity check
            if((memory1_instru->arg1 < 0) || (memory1_instru->arg1 > 9999)){
                printf("Memory 1 breach LOAD.\n");
            }
        }

        //STORE
        if(memory1_instru->op_code==9)
        {

            //sanity check
            if((memory1_instru->arg1 < 0) || (memory1_instru->arg1 > 9999)){
                printf("Memory 1 breach STORE.\n\n\n\n\n");
            }
        }

        //printf("   Execute Memory 1: %d:%d:%d:%d:%d:%d:%d:%d\n\n",memory1_instru->op_code,memory1_instru->arg1,memory1_instru->arg1_addr,memory1_instru->arg2,memory1_instru->arg2_addr,memory1_instru->arg3,memory1_instru->arg3_addr,memory1_instru->pc);
        return execute_memory1_pc;
    }
    else
    {
        memory1_instru=NULL;
        return -1;
    }

}

//MEMORY FU 2 EXECUTE
int execute_memory2(){
        //no instruction to get from decode
        if(memory1_instru==NULL)
        {
            printf("No instructions to execute_memory 2.\n\n");
            memory2_instru=NULL;
            return -1;
        }

        //branching
        if(pc_update!=INT_MAX)
        {
            printf("STALL Due to branch  execute_memory 2.\n\n");
            memory2_instru=NULL;
            return -1;
        }

    //no stall
        if(dependent_flag!=1)
        {

            //process instruction from decode to execute_memory stage
            memory2_instru=memory1_instru;
            memory1_instru=NULL;
            int execute_memory_pc=memory2_instru->pc-20000;

            printf("\nPC execute_memory 2:%d  Instruction: %s", execute_memory_pc,instruction[execute_memory_pc]);

            //printf("   Execute Memory 2: %d:%d:%d:%d:%d:%d:%d:%d\n\n",memory2_instru->op_code,memory2_instru->arg1,memory2_instru->arg1_addr,memory2_instru->arg2,memory2_instru->arg2_addr,memory2_instru->arg3,memory2_instru->arg3_addr,memory2_instru->pc);
			return execute_memory_pc;
        }
        else
        {
            return -1;
        }

}

//MEMORY FU 3 EXECUTE
int execute_memory3(){
        //no instruction to get from decode
        if(memory2_instru==NULL)
        {
            printf("No instructions to execute_memory 3.\n\n");
            memory3_instru=NULL;
            return -1;
        }

        //branching
        if(pc_update!=INT_MAX)
        {
            printf("STALL Due to branch  execute_memory 3.\n\n");
            memory3_instru=NULL;
            return -1;
        }

    //no stall
        if(dependent_flag!=1)
        {
            //process instruction from decode to execute_memory stage
            memory3_instru=memory2_instru;
            int execute_memory_pc=memory3_instru->pc-20000;

            if(memory3_instru->op_code==9){
                int i;
                for(i=0;i<15;i++)
                {
                    ROB[i]=ROB[i+1];
                }
                ROB[15]=NULL;
            }

            printf("\nPC execute_memory 3:%d  Instruction: %s", execute_memory_pc,instruction[execute_memory_pc]);

            //LOAD
            if(memory3_instru->op_code==8)
            {
                //sanity check
                if((memory3_instru->arg1 < 0) || (memory3_instru->arg1 > 9999)){
                    printf("Memory 3 breach LOAD.\n");
                }
                else{
                    memory3_instru->arg1=mem[memory3_instru->arg1];
                    printf("memory 3: %d\n",mem[memory3_instru->arg1]);
                }
            }

            //STORE
            if(memory3_instru->op_code==9)
            {
                //sanity check
                if((memory3_instru->arg1 < 0) || (memory3_instru->arg1 > 9999)){
                    printf("Memory 3 breach STORE.\n\n\n\n\n");
                }
                else{
                        if(memory3_instru->arg1_addr==-1)
                        mem[memory3_instru->arg1]=R[memory3_instru->arf_addr]; //ankush
                        else
                            mem[memory3_instru->arg1]=PRF[memory3_instru->arg1_addr];
                }
            }

            //reset reg status of dest reg for insts till LOAD
            if(memory3_instru->op_code==8)
            {
                PRF[memory3_instru->arg1_addr]=memory3_instru->arg1;
            }

            //printf("   Execute Memory 3: %d:%d:%d:%d:%d:%d:%d:%d\n\n",memory3_instru->op_code,memory3_instru->arg1,memory3_instru->arg1_addr,memory3_instru->arg2,memory3_instru->arg2_addr,memory3_instru->arg3,memory3_instru->arg3_addr,memory3_instru->pc);
			return execute_memory_pc;
        }
        else
        {
            return -1;
        }

}

//WRITE BACK stage
int write_back(){

	//get next instruction from one of multiple FUs

    if(memory3_instru!=NULL && memory3_instru->op_code==8)
    {
        wb_instru=memory3_instru;
        memory3_instru=NULL;
        flag_INTstall=1;
        flag_MULstall=1;
    } else if(int_instru!=NULL)
    {
        wb_instru=int_instru;
        int_instru=NULL;
        flag_MULstall=1;
        flag_INTstall=0;
    }
    else if(mul4_instru!=NULL)
    {
        flag_INTstall=0;
        flag_MULstall=0;

        wb_instru=mul4_instru;
        mul4_instru=NULL;
        mul3_instru=NULL;
        mul2_instru=NULL;
        mul1_instru=NULL;

        flag_MULoccupied=0;
    }
    else
    {
        printf("No instructions to write back.\n\n");
        wb_instru=NULL;
        flag_MULstall=0;
        flag_INTstall=0;
        return -1;
    }


	int wb_pc=wb_instru->pc-20000;

    printf("\nPC write back:%d  Instruction: %s\n", wb_pc,instruction[wb_pc]);

    if(wb_instru->op_code<9 || wb_instru->op_code==13)
    {
        PRF_status[wb_instru->arg1_addr]=0; //valid now - can be used by new
        printf("Tag for data forwarding: %d\n",wb_instru->arg1_addr);
        printf("Value forwarded: %d\n\n",PRF[wb_instru->arg1_addr]);
    }

    data_forwarding();

    wb_instru=NULL;
    return wb_pc;
}

//commit stage
int commit(){
    //no instructions to get from write back stage

    flag_INTstall=0;
    flag_MULstall=0;

	if(ROB[0]==NULL)
	{
        //printf("No instructions to commit.\n");
		commit_instru=NULL;
		return -1;
	}

    //in case of HALT, free pointers and exit
    if(ROB[0]->op_code==14)
    {
        func_exit();
        printf("\n**********Terminating bcoz of HALT**********\n\n");
        display();
        printf("\nNumber of cycles done: %d\n",cycles_done);
        exit(0);
    }

    if(ROB[0]->op_code>9 && ROB[0]->op_code<13)
    {
        commit_instru=ROB[0];
        int commit_pc=commit_instru->pc-20000;
        printf("\nCommit:%s",instruction[commit_pc]);
        int i;
        for(i=0;i<15;i++)
        {
            ROB[i]=ROB[i+1];
        }
        ROB[15]=NULL;
        commit_instru=NULL;
        return commit_pc;
    }

    if( (ROB[0]->op_code==13 || ROB[0]->op_code<9) && PRF_status[ROB[0]->arg1_addr]==0)
    {
        wb_instru=NULL;
        commit_instru=ROB[0];

        int i;
        for(i=0;i<15;i++)
        {
            ROB[i]=ROB[i+1];
        }
        ROB[15]=NULL;

        //process next inst from write back

        int commit_pc=commit_instru->pc-20000;

        //printf("dependent_reg=%d\n",dependent_reg);
        //printf("commit_instru->arg1_addr= %d\n",commit_instru->arg1_addr);


        //remove dependency dependency flag & reg
        if(dependent_reg==commit_instru->arg1_addr )
        {
            dependent_flag = 0;
            dependent_reg = -1;
            //printf("dependent_flag=%d\n",dependent_flag);
        }


        if((commit_instru->op_code==13 ||commit_instru->op_code<9) && PRF_status[commit_instru->arg1_addr]==0)
        {

            if(commit_instru->arf_addr==8)
            {
                X=PRF[commit_instru->arg1_addr];
            }
            else
            {
                if(commit_instru->arf_addr>-1)
                {
                    R[commit_instru->arf_addr]=PRF[commit_instru->arg1_addr];
                }
            }

            for(i=0;i<16;i++)
            {
                if(free_list[i]==-1)
                {
                    free_list[i]=commit_instru->arg1_addr;
                    break;
                }
            }
            AL[commit_instru->arg1_addr]=0;
            if(renamed_array[commit_instru->arg1_addr]==0)
            {
                rename_table[commit_instru->arf_addr]= -1;
            }

        }
        commit_instru=NULL;
        return commit_pc;
    }
    else
    {
        commit_instru=NULL;
		return -1;
	}

}

//display menu choice
void display(){
	int i=0;

    if(pc_commit==-1)
	{
		printf("\n\nNo instructions in commit stage.\n");
	}
	else
	{
		printf("Instruction in commit: %s\n",instruction[pc_commit]);
	}

	if(pc_wb==-1)
	{
		printf("No instructions in write back stage.\n");
	}
	else
	{
		printf("Instruction in write back: %s\n",instruction[pc_wb]);
	}


	if(pc_mul4==-1)
	{
		printf("No instructions in mul 4 stage.\n");
	}
	else
	{
		printf("Instruction in mul 4: %s\n",instruction[pc_mul4]);
	}

	if(pc_mul3==-1)
	{
		printf("No instructions in mul 3 stage.\n");
	}
	else
	{
		printf("Instruction in mul 3: %s\n",instruction[pc_mul3]);
	}

    if(pc_mul2==-1)
	{
		printf("No instructions in mul 2 stage.\n");
	}
	else
	{
		printf("Instruction in mul 2: %s\n",instruction[pc_mul2]);
	}

    if(execute_mul1pc==-1)
	{
		printf("No instructions in mul 1 stage.\n");
	}
	else
	{
		printf("Instruction in mul 1: %s\n",instruction[execute_mul1pc]);
	}

	if(pc_memory3==-1)
	{
		printf("No instructions in memory 3 stage.\n");
	}
	else
	{
		printf("Instruction in memory 3: %s\n",instruction[pc_memory3]);
	}

    if(pc_memory2==-1)
	{
		printf("No instructions in memory 2 stage.\n");
	}
	else
	{
		printf("Instruction in memory 2: %s\n",instruction[pc_memory2]);
	}

    if(execute_memory1pc==-1)
	{
		printf("No instructions in memory 1 stage.\n");
	}
	else
	{
		printf("Instruction in memory 1: %s\n",instruction[execute_memory1pc]);
	}

    if(execute_intpc==-1)
	{
		printf("No instructions in int stage.\n");
	}
	else
	{
		printf("Instruction in int stage: %s\n",instruction[execute_intpc]);
	}

	if(pc_decode2==-1)
	{
		printf("No instructions in decode stage 2.\n");
	}
	else
	{
		printf("Instruction in decode stage 2: %s\n",instruction[pc_decode2]);
	}

	if(pc_decode1==-1)
	{
		printf("No instructions in decode stage 1.\n");
	}
	else
	{
		printf("Instruction in decode stage 1: %s\n",instruction[pc_decode1]);
	}

	if(pc_fetch2==-1)
	{
		printf("No instructions in fetch stage 2.\n");
	}
	else
	{
		printf("Instruction in fetch stage 2: %s\n",instruction[pc_fetch2]);
	}

	if(pc_fetch1==-1)
	{
		printf("No instructions in fetch stage 1.\n");
	}
	else
	{
		printf("Instruction in fetch stage 1: %s\n",instruction[pc_fetch1]);
	}
    printf("IQ Entries:\n");
    for(i=0;i<8;i++)
    {
        if(IQ[i]!=NULL)
        {
            printf("IQ[%d]= %s\n",i,instruction[IQ[i]->pc-20000]);
        }
    }
    printf("\nLSQ Entries:\n");
    for(i=0;i<4;i++)
    {
        if(LSQ[i]!=NULL)
        {
            printf("LSQ[%d]= %s\n",i,instruction[LSQ[i]->pc-20000]);
        }
    }
    printf("\nROB Entries:\n");
    for(i=0;i<16;i++)
    {
        if(ROB[i]!=NULL)
        {
            printf("ROB[%d]= %s\n",i,instruction[ROB[i]->pc-20000]);
        }
    }

	printf("\nARF:\n");
	for(i=0;i<8;i++)
	{
		printf("R[%d]:%d  ",i,R[i]);
	}
	printf("X: %d\n",X);

    //Physical registers
	printf("\nPRF:\n");
	for(i=0;i<16;i++)
	{
		printf("PRF[%d]:%d:%d  ",i,PRF[i],PRF_status[i]);
		if((i+1)%4==0)
			printf("\n");
	}

    //rename_table[9];
	printf("\nRename Table:\n");
	for(i=0;i<9;i++)
	{
		printf("R[%d]:P[%d]  ",i,rename_table[i]);
		if((i+1)%6==0)
			printf("\n");
	}

    //free_list[16];
	printf("\n\nFree List\n");
	for(i=0;i<16;i++)
	{
		printf("[%d]:%d  ",i,free_list[i]);
		if((i+1)%8==0)
			printf("\n");
	}

    //AL[16];
	printf("\n\nAllocation List.\n");
   	for(i=0;i<16;i++)
	{
		printf("AL[%d]:%d  ",i,AL[i]);
		if((i+1)%6==0)
			printf("\n");
	}

    //renamed_array[16];
    printf("\n\nRenamed Array:\n");
   	for(i=0;i<16;i++)
	{
		printf("[%d]:%d  ",i,renamed_array[i]);
		if((i+1)%8==0)
			printf("\n");
	}

    printf("\nMemory matrix: \n\n");
//print memory matrix
	for(i=0;i<=20;i++)
	{
		printf("mem[%d]:%d  ",i,mem[i]);
		if((i+1)%6==0)
			printf("\n");
	}
}

//simulate menu choice
void simulate(int num_cycl){
    //reset program counters
    pc_commit=-1;
    pc_wb=-1;
    pc_execute=-1;

    pc_int=-1;

    pc_mul4=-1;
    pc_mul3=-1;
    pc_mul2=-1;
    pc_mul1=-1;

    pc_memory3=-1;
    pc_memory2=-1;
    pc_memory1=-1;

    pc_decode2=-1;
    pc_decode1=-1;
    pc_fetch2=-1;
    pc_fetch1=-1;

    execute_intpc=-1;
    execute_mul1pc=-1;
    execute_memory1pc=-1;

    while(num_cycl!=0)
    {
        pc_commit=commit();
        pc_wb=write_back();

        pc_memory3=execute_memory3();
        pc_memory2=execute_memory2();

        pc_mul4=execute_mul4();
        pc_mul3=execute_mul3();
        pc_mul2=execute_mul2();

        pc_execute=execute();
        //IQ_handling();
        pc_decode2=decode_stage2();
        pc_decode1=decode_stage1();
        pc_fetch2=fetch_stage2();
        pc_fetch1=fetch_stage1();

        //total no. of cycles done
        if(flag_halt!=1) //if halt clock frozen
            cycles_done++;

        num_cycl--;

//		printf("Cycles : %d\n\n",num_cycl);

        printf("\n**************\n");
    }
    display();
}

//to convert case to lower of user choice
char * strlwr(char * s){
	char *t =s;
	if (!s)
	{
		return 0;
	}
	while (*t!='\0')
	{
		if(*t>='A'&&*t<='Z')
		{
			*t=*t+('a'-'A');
		}
		t++;
	}
	return s;
}

//main func for user choice menu
int main(){
	char *tok,choice[15],tempcmd[9];
	int num_cycles=0;
	memset(tempcmd,'\0',sizeof(tempcmd));
	printf("---------------------------Starting the Program------------------------------\n");

    //call initialize once in the beginning
    initialize();

	while(1){
        printf("\n-----------------------\n");
		printf("Enter command : ");
		gets(choice);
		printf("\n-----------------------\n");
		strcpy(choice,strlwr(choice));


		if(strcmp(choice,"initialize")==0){
			initialize();
		}

		else if(strcmp(choice,"display")==0){
			display();
		}

		else if(strcmp(choice,"exit")==0){
			return 1;
		}

		else{
			strncpy(tempcmd,choice,8);
			if((strcmp(tempcmd,"simulate")==0) && (choice[8]==' '))
			{
				tok = strtok(choice," ");
				tok = strtok(NULL," ");
				num_cycles = atoi(tok);
				simulate(num_cycles);
				printf("\n\nCycles_done: %d\n",cycles_done);
			}

			else
			{
				printf("Wrong Input\n");
			}
		}

	}
	func_exit();
	return 0;
}
