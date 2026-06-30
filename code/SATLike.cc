#include "SATLike.h"
#include "MaxSAT.h"

bool Satlike::if_using_neighbor = true;

Satlike::Satlike() : mse21(Torc::Instance()->GetSatlikeMimicMse21()) {}

void Satlike::settings()
{
    cutoff_time = 10;
    max_flips = Torc::Instance()->GetSatlikeMaxFlips();    
    max_non_improve_flip = Torc::Instance()->GetSatlikeMaxNonImproveFlip();
    cout << "c max_flips = " << max_flips << "; max_non_improve_flip = " << max_non_improve_flip << endl;	
    if (Torc::Instance()->GetSatlikeMaxFlipsReduceBeyondClsNum() != 0 && num_clauses > Torc::Instance()->GetSatlikeMaxFlipsReduceBeyondClsNum())
	{
		const double reduceFactor = double(num_clauses)/(double)Torc::Instance()->GetSatlikeMaxFlipsReduceBeyondClsNum();
		auto Reduce = [&](int& r)
		{
			r = (int)((double)r/reduceFactor);
		};
		Reduce(max_flips);
		Reduce(max_non_improve_flip);	
		cout << "c maxflips&max_non_improve_flip reduced: max_flips = " << max_flips << "; max_non_improve_flip = " << max_non_improve_flip << endl;	
	}
	
    max_tries = 100000000;
    if (problem_weighted == 1)
    {
        cout << "c problem weighted = 1" << endl;
                
        large_clause_count_threshold = 0;
        soft_large_clause_count_threshold = 0;

        rdprob = 0.01;
        hd_count_threshold = 15;
        rwprob = 0.1;
        smooth_probability = 0.01;

        if ((top_clause_weight / num_sclauses) > 10000)
        {
            h_inc = 300;
            softclause_weight_threshold = 500;
        }
        else
        {
            h_inc = 3;
            softclause_weight_threshold = 0;
        }

        if (num_vars > 2000)
        {
            rdprob = 0.01;
            hd_count_threshold = 15;
            rwprob = 0.1;
            smooth_probability = 0.0001;
        }
    }
    else
    {
        cout << "c problem weighted = 0" << endl;
        
        large_clause_count_threshold = 0;
        soft_large_clause_count_threshold = 0;

        rdprob = 0.01;
        hd_count_threshold = 42;
        rwprob = 0.091;
        smooth_probability = 0.000003;

        h_inc = 1;
        softclause_weight_threshold = mse21 ? 400 : 600;

        if (num_vars < 1100) //for somall instances
        {
            h_inc = 1;
            softclause_weight_threshold = 0;
            rdprob = 0.01;
            hd_count_threshold = 15;
            rwprob = 0;
            smooth_probability = 0.01;
            return;
        }
    }
}

void Satlike::allocate_memory()
{
    int malloc_var_length = num_vars + 10;
    int malloc_clause_length = num_clauses + 10;

    unit_clause = new lit[malloc_clause_length];

    var_lit = new lit *[malloc_var_length];
    var_lit_count = new int[malloc_var_length];
    //clause_lit = new lit *[malloc_clause_length];
    //clause_lit_count = new int[malloc_clause_length];

    score = new long long[malloc_var_length];
    var_neighbor = new int *[malloc_var_length];
    var_neighbor_count = new int[malloc_var_length];
    time_stamp = new long long[malloc_var_length];
    neighbor_flag = new int[malloc_var_length];
    temp_neighbor = new int[malloc_var_length];

    //org_clause_weight = new long long[malloc_clause_length];
    clause_weight = new long long[malloc_clause_length];
    sat_count = new int[malloc_clause_length];
    sat_var = new int[malloc_clause_length];
    clause_selected_count = new long long[malloc_clause_length];
    best_soft_clause = new int[malloc_clause_length];

    hardunsat_stack = new int[malloc_clause_length];
    index_in_hardunsat_stack = new int[malloc_clause_length];
    softunsat_stack = new int[malloc_clause_length];
    index_in_softunsat_stack = new int[malloc_clause_length];

    unsatvar_stack = new int[malloc_var_length];
    index_in_unsatvar_stack = new int[malloc_var_length];
    unsat_app_count = new int[malloc_var_length];

    goodvar_stack = new int[malloc_var_length];
    already_in_goodvar_stack = new int[malloc_var_length];
    
    if (mse21)
    {
		score_change_stack = new int[malloc_var_length];
		if_score_change = new bool[malloc_var_length];
	}

    cur_soln = new int[malloc_var_length];
    best_soln = new int[malloc_var_length];
    local_opt_soln = new int[malloc_var_length];

    large_weight_clauses = new int[malloc_clause_length];
    soft_large_weight_clauses = new int[malloc_clause_length];
    already_in_soft_large_weight_stack = new int[malloc_clause_length];

    best_array = new int[malloc_var_length];
    temp_lit = new int[malloc_var_length];
}

void Satlike::free_memory()
{
    int i;
    for (i = 0; i < num_clauses; i++)
        delete[] clause_lit[i];

    for (i = 1; i <= num_vars; ++i)
    {
        delete[] var_lit[i];
        delete[] var_neighbor[i];
    }

    delete[] var_lit;
    delete[] var_lit_count;
    delete[] clause_lit;
    delete[] clause_lit_count;

    delete[] score;
    delete[] var_neighbor;
    delete[] var_neighbor_count;
    delete[] time_stamp;
    delete[] neighbor_flag;
    delete[] temp_neighbor;

    delete[] org_clause_weight;
    delete[] clause_weight;
    delete[] sat_count;
    delete[] sat_var;
    delete[] clause_selected_count;
    delete[] best_soft_clause;

    delete[] hardunsat_stack;
    delete[] index_in_hardunsat_stack;
    delete[] softunsat_stack;
    delete[] index_in_softunsat_stack;

    delete[] unsatvar_stack;
    delete[] index_in_unsatvar_stack;
    delete[] unsat_app_count;

    delete[] goodvar_stack;
    delete[] already_in_goodvar_stack;
    if (mse21)
    {
		delete[] if_score_change;
		delete[] score_change_stack;		
	}

    //delete [] fix;
    delete[] cur_soln;
    delete[] best_soln;
    delete[] local_opt_soln;

    delete[] large_weight_clauses;
    delete[] soft_large_weight_clauses;
    delete[] already_in_soft_large_weight_stack;

    delete[] best_array;
    delete[] temp_lit;
}

bool Satlike::build_neighbor_relation()
{
    int i, j, count;
    int v, c, n;
    int temp_neighbor_count;    

    for (v = 1; v <= num_vars; ++v)
    {
        neighbor_flag[v] = 1;
        temp_neighbor_count = 0;

        for (i = 0; i < var_lit_count[v]; ++i)
        {
            c = var_lit[v][i].clause_num;
            for (j = 0; j < clause_lit_count[c]; ++j)
            {
                n = clause_lit[c][j].var_num;
                if (neighbor_flag[n] != 1)
                {
                    neighbor_flag[n] = 1;
                    temp_neighbor[temp_neighbor_count++] = n;
                }
            }
        }

        neighbor_flag[v] = 0;

        var_neighbor[v] = new (std::nothrow) int[temp_neighbor_count];
        if (var_neighbor[v] == nullptr)
		{
			for (j = 0; j < v; ++j)
			{
				free(var_neighbor[v]);
				var_neighbor[v]  = nullptr;
			}
			return false;
		}
		
        var_neighbor_count[v] = temp_neighbor_count;

        count = 0;
        for (i = 0; i < temp_neighbor_count; i++)
        {
            var_neighbor[v][count++] = temp_neighbor[i];
            neighbor_flag[temp_neighbor[i]] = 0;
        }
        
        if (Torc::Instance()->GetSatlikeInitTimeThr() != 0 && v % 1000 == 0 && get_runtime() >= Torc::Instance()->GetSatlikeInitTimeThr())
        {
			for (j = 0; j <= v; ++j)
			{
				free(var_neighbor[v]);
				var_neighbor[v]  = nullptr;
			}
			return false;
		}
    }
    return true;
}

void Satlike::build_instance(char *filename)
{
    istringstream iss;
    string line;
    char tempstr1[10];
    char tempstr2[10];

    ifstream infile(filename);

    /*** build problem data structures of the instance ***/
    while (getline(infile, line))
    {
        if (line[0] == 'p')
        {
            int read_items;
            num_vars = num_clauses = 0;
            read_items = sscanf(line.c_str(), "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);

            if (read_items < 5)
            {
                cout << "read item < 5 " << endl;
                exit(-1);
            }
            break;
        }
    }

    allocate_memory();

    int v, c;
    for (c = 0; c < num_clauses; c++)
    {
        clause_lit_count[c] = 0;
        clause_lit[c] = NULL;
    }
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit_count[v] = 0;
        var_lit[v] = NULL;
        var_neighbor[v] = NULL;
    }

    int cur_lit;
    c = 0;
    problem_weighted = 0;
    partial = 0;
    num_hclauses = num_sclauses = 0;
    max_clause_length = 0;
    min_clause_length = 100000000;
    unit_clause_count = 0;

    int *redunt_test = new int[num_vars + 1];
    memset(redunt_test, 0, sizeof(int) * num_vars + 1);
    //Now, read the clauses, one at a time.
    while (getline(infile, line))
    {
        if (line[0] == 'c')
            continue;
        else
        {
            iss.clear();
            iss.str(line);
            iss.seekg(0, ios::beg);
        }
        clause_lit_count[c] = 0;

        iss >> org_clause_weight[c];
        if ((unsigned long long)org_clause_weight[c] != top_clause_weight)
        {
            if (org_clause_weight[c] != 1)
                problem_weighted = 1;
            total_soft_weight += org_clause_weight[c];
            num_sclauses++;
        }
        else
        {
            num_hclauses++;
            partial = 1;
        }

        iss >> cur_lit;
        int clause_reduent = 0;
        while (cur_lit != 0)
        {
            if (redunt_test[abs(cur_lit)] == 0)
            {
                temp_lit[clause_lit_count[c]] = cur_lit;
                clause_lit_count[c]++;
                redunt_test[abs(cur_lit)] = cur_lit;
            }
            else if (redunt_test[abs(cur_lit)] != cur_lit)
            {
                clause_reduent = 1;
                break;
            }
            iss >> cur_lit;
        }
        if (clause_reduent == 1)
        {
            for (int i = 0; i < clause_lit_count[c]; ++i)
                redunt_test[abs(temp_lit[i])] = 0;

            num_clauses--;
            clause_lit_count[c] = 0;
            continue;
        }

        clause_lit[c] = new lit[clause_lit_count[c] + 1];

        int i;
        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            clause_lit[c][i].clause_num = c;
            clause_lit[c][i].var_num = abs(temp_lit[i]);
            redunt_test[abs(temp_lit[i])] = 0;
            if (temp_lit[i] > 0)
                clause_lit[c][i]
                    .sense = 1;
            else
                clause_lit[c][i].sense = 0;

            var_lit_count[clause_lit[c][i].var_num]++;
        }
        clause_lit[c][i].var_num = 0;
        clause_lit[c][i].clause_num = -1;

        if (clause_lit_count[c] == 1)
            unit_clause[unit_clause_count++] = clause_lit[c][0];

        if (clause_lit_count[c] > max_clause_length)
            max_clause_length = clause_lit_count[c];

        if (clause_lit_count[c] < min_clause_length)
            min_clause_length = clause_lit_count[c];

        c++;
    }

    infile.close();

    //creat var literal arrays
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit[v] = new lit[var_lit_count[v] + 1];
        var_lit_count[v] = 0; //reset to 0, for build up the array
    }
    //scan all clauses to build up var literal arrays
    for (c = 0; c < num_clauses; ++c)
    {
        for (int i = 0; i < clause_lit_count[c]; ++i)
        {
            v = clause_lit[c][i].var_num;
            var_lit[v][var_lit_count[v]] = clause_lit[c][i];
            ++var_lit_count[v];
        }
    }
    for (v = 1; v <= num_vars; ++v)
        var_lit[v][var_lit_count[v]].clause_num = -1;

    build_neighbor_relation();

    best_soln_feasible = 0;
    opt_unsat_weight = total_soft_weight + 1;
}

void Satlike::build_instance(int numVars, int numClauses, unsigned long long topClauseweight, lit **satlike_clause, int *satlike_clause_lit_count, long long *satlike_clause_weight)
{
    /*** build problem data structures of the instance ***/
    start_timing();

    num_vars = numVars;
    num_clauses = numClauses;
    top_clause_weight = topClauseweight;
    clause_lit = satlike_clause;
    clause_lit_count = satlike_clause_lit_count;
    org_clause_weight = satlike_clause_weight;

    allocate_memory();
    int v;
    cout << "c " << num_vars << " " << num_clauses << endl;
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit_count[v] = 0;
        var_lit[v] = NULL;
        var_neighbor[v] = NULL;
    }

    problem_weighted = 0;
    partial = 0;
    num_hclauses = num_sclauses = 0;
    max_clause_length = 0;
    min_clause_length = 100000000;
    unit_clause_count = 0;
    //int *redunt_test = new int[num_vars + 1];
    //memset(redunt_test, 0, sizeof(int) * num_vars + 1);
    //Now, read the clauses, one at a time.
    for (int i = 0; i < num_clauses; ++i)
    {
        for (int j = 0; j < clause_lit_count[i]; ++j)
        {
            //int temv = clause_lit[i][j].var_num;
            //int temsense = clause_lit[i][j].sense;
            var_lit_count[clause_lit[i][j].var_num]++;
        }

        if ((unsigned long long)org_clause_weight[i] != top_clause_weight)
        {
            if (org_clause_weight[i] != 1)
                problem_weighted = 1;
            total_soft_weight += org_clause_weight[i];
            num_sclauses++;
        }
        else
        {
            num_hclauses++;
            partial = 1;
        }
        if (clause_lit_count[i] == 1)
            unit_clause[unit_clause_count++] = clause_lit[i][0];

        if (clause_lit_count[i] > max_clause_length)
            max_clause_length = clause_lit_count[i];

        if (clause_lit_count[i] < min_clause_length)
            min_clause_length = clause_lit_count[i];
    }
    cout << "c before creat var literal arrays " << endl;
    //creat var literal arrays
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit[v] = new lit[var_lit_count[v] + 1];
        var_lit_count[v] = 0; //reset to 0, for build up the array
    }
    //scan all clauses to build up var literal arrays
    for (int i = 0; i < num_clauses; ++i)
    {
        for (int j = 0; j < clause_lit_count[i]; ++j)
        {
            v = clause_lit[i][j].var_num;
            var_lit[v][var_lit_count[v]] = clause_lit[i][j];
            ++var_lit_count[v];
        }
    }

    for (v = 1; v <= num_vars; ++v)
        var_lit[v][var_lit_count[v]].clause_num = -1;

    cout << "c build time before building neighborhood relations is " << get_runtime() << "; #clauses = " << num_clauses << endl;

	if (if_using_neighbor)
	{
		if ((Torc::Instance()->GetSatlikePreInitTimeThr() != 0 && get_runtime() > Torc::Instance()->GetSatlikePreInitTimeThr()) || num_clauses > Torc::Instance()->GetSatlikePreInitMaxClss())
		{
			cout << "c skipping neighborhood relations, since " << (num_clauses > Torc::Instance()->GetSatlikePreInitMaxClss() ? "too many clauses" : "run-time over 1 sec.") << endl;
			if_using_neighbor = false;
		}
		else
		{
			cout << "c before creating neighborhood relations" << endl;
			if_using_neighbor = build_neighbor_relation();    
			cout << "c run-time after creating neighborhood relations is " << get_runtime() << endl;   
			if (!if_using_neighbor)
			{
				cout << "c Neighborhood relations abandonded, because of memory-out or time-threshold" << endl;
			}			 
		}
	}
	else
	{
		cout << "c skipping neighborhood relations, since it was decided to be skipped in one of the previous invocations" << endl;
	}
    best_soln_feasible = 0;
    opt_unsat_weight = total_soft_weight + 1;
}

void Satlike::init(vector<int> &init_solution)
{
    soft_large_weight_clauses_count = 0;
    //Initialize clause information
    for (int c = 0; c < num_clauses; c++)
    {
        already_in_soft_large_weight_stack[c] = 0;
        clause_selected_count[c] = 0;

        if ((unsigned long long)org_clause_weight[c] == top_clause_weight)
            clause_weight[c] = 1;
        else
        {
			if (mse21)
			{
				 clause_weight[c] = org_clause_weight[c];
			}
			else
			{
				if (problem_weighted == 1)
				{
					clause_weight[c] = 10 * org_clause_weight[c];
				}
				else clause_weight[c] = 100 * org_clause_weight[c];
			}
            
            if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
        }
    }

    //init solution
    if (init_solution.size() == 0)
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    else
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = init_solution[v];
            if (cur_soln[v] != 0 && cur_soln[v] != 1)
                cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }

    //init stacks
    hard_unsat_nb = 0;
    soft_unsat_weight = 0;
    hardunsat_stack_fill_pointer = 0;
    softunsat_stack_fill_pointer = 0;
    unsatvar_stack_fill_pointer = 0;
    large_weight_clauses_count = 0;

    /* figure out sat_count, sat_var and init unsat_stack */
    for (int c = 0; c < num_clauses; ++c)
    {
        sat_count[c] = 0;
        for (int j = 0; j < clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                sat_count[c]++;
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }
        if (sat_count[c] == 0)
        {
            unsat(c);
        }
    }

    /*figure out score*/
    for (int v = 1; v <= num_vars; v++)
    {
        score[v] = 0;
        for (int i = 0; i < var_lit_count[v]; ++i)
        {
            int c = var_lit[v][i].clause_num;
            if (sat_count[c] == 0)
                score[v] += clause_weight[c];
            else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
                score[v] -= clause_weight[c];
        }
    }

    //init goodvars stack
    goodvar_stack_fill_pointer = 0;
    if (mse21) score_change_stack_fill_pointer = 0;
    for (int v = 1; v <= num_vars; v++)
    {
		if (mse21) if_score_change[v] = false;
        if (score[v] > 0)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = -1;
    }
}

void Satlike::increase_weights()
{
    int i, c, v;
    for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
    {
        c = hardunsat_stack[i];
        clause_weight[c] += h_inc;

        if (clause_weight[c] == (h_inc + 1))
            large_weight_clauses[large_weight_clauses_count++] = c;

        for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
        {
            score[v] += h_inc;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
    }
    for (i = 0; i < softunsat_stack_fill_pointer; ++i)
    {
        c = softunsat_stack[i];
        if (clause_weight[c] > softclause_weight_threshold)
            continue;
        else
            clause_weight[c]++;

        if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
        {
            already_in_soft_large_weight_stack[c] = 1;
            soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
        }
        for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
        {
            score[v]++;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
    }
}

void Satlike::smooth_weights()
{
    int i, clause, v;

    for (i = 0; i < large_weight_clauses_count; i++)
    {
        clause = large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= h_inc;

            if (clause_weight[clause] == 1)
            {
                large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v] += h_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }

    for (i = 0; i < soft_large_weight_clauses_count; i++)
    {
        clause = soft_large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause]--;
            if (clause_weight[clause] == 1 && already_in_soft_large_weight_stack[clause] == 1)
            {
                already_in_soft_large_weight_stack[clause] = 0;
                soft_large_weight_clauses[i] = soft_large_weight_clauses[--soft_large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v]++;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
}

void Satlike::update_clause_weights()
{
    if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && large_weight_clauses_count > large_clause_count_threshold)
    {
        smooth_weights();
    }
    else
    {
        increase_weights();
    }
}

int Satlike::pick_var()
{
    int i, v;
    int best_var;

    if (goodvar_stack_fill_pointer > 0)
    {
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
            return goodvar_stack[rand() % goodvar_stack_fill_pointer];

        if (goodvar_stack_fill_pointer < hd_count_threshold)
        {
            best_var = goodvar_stack[0];
            for (i = 1; i < goodvar_stack_fill_pointer; ++i)
            {
                v = goodvar_stack[i];
                if (score[v] > score[best_var])
                    best_var = v;
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                        best_var = v;
                }
            }
            return best_var;
        }
        else
        {
            best_var = goodvar_stack[rand() % goodvar_stack_fill_pointer];
            for (i = 1; i < hd_count_threshold; ++i)
            {
                v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
                if (score[v] > score[best_var])
                    best_var = v;
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                        best_var = v;
                }
            }
            return best_var;
        }
    }

    update_clause_weights();

    int sel_c;
    lit *p;

    if (hardunsat_stack_fill_pointer > 0)
    {
        sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
    }
    else
    {
        sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
    }
    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
        return clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;

    best_var = clause_lit[sel_c][0].var_num;
    p = clause_lit[sel_c];
    for (p++; (v = p->var_num) != 0; p++)
    {
        if (score[v] > score[best_var])
            best_var = v;
        else if (score[v] == score[best_var])
        {
            if (time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }
    }

    return best_var;
}

void Satlike::local_search(vector<int> &init_solution)
{
    cout << "c changing to SATLike solver! " << endl;
    settings();
    for (tries = 1; tries < max_tries; ++tries)
    {
        init(init_solution);
        
        if (if_using_neighbor || !mse21)
        {
			for (step = 1; step < max_flips; ++step)
			{
				if (hard_unsat_nb == 0 && (soft_unsat_weight < opt_unsat_weight || best_soln_feasible == 0))
				{
					max_flips = step + max_non_improve_flip;
					if (soft_unsat_weight < opt_unsat_weight)
					{
						best_soln_feasible = 1;
						opt_unsat_weight = soft_unsat_weight;
						opt_time = get_runtime();
						for (int v = 1; v <= num_vars; ++v)
							best_soln[v] = cur_soln[v];
					}
					if (opt_unsat_weight == 0)
						return;
				}
				int flipvar = pick_var();
				flip(flipvar);
				time_stamp[flipvar] = step;
			}
		}
		else
		{
			for (step = 1; step < max_flips; ++step)
            {
                if (hard_unsat_nb == 0 && (soft_unsat_weight < opt_unsat_weight || best_soln_feasible == 0))
                {
                    max_flips = step + max_non_improve_flip;
                    if (soft_unsat_weight < opt_unsat_weight)
                    {
                        best_soln_feasible = 1;
                        opt_unsat_weight = soft_unsat_weight;
                        opt_time = get_runtime();
                        for (int v = 1; v <= num_vars; ++v)
                            best_soln[v] = cur_soln[v];
                    }
                    if (opt_unsat_weight == 0)
                        return;
                }
                int flipvar = pick_var();
                flip2(flipvar);
                time_stamp[flipvar] = step;
            }
		}
    }
}

void Satlike::update_goodvarstack1(int flipvar)
{
	if (mse21)
	{
		  int v;
		//remove the vars no longer goodvar in goodvar stack
		for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
		{
			v = goodvar_stack[index];
			if (score[v] <= 0)
			{
				goodvar_stack[index] = mypop(goodvar_stack);
				already_in_goodvar_stack[goodvar_stack[index]] = index;
				already_in_goodvar_stack[v] = -1;
			}
		}

		//add goodvar
		for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
		{
			v = var_neighbor[flipvar][i];
			if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
			{
				already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
				mypush(v, goodvar_stack);
			}
		}
	} 
	else
	{
		int v;
		//remove the vars no longer goodvar in goodvar stack
		for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
		{
			v = goodvar_stack[index];
			if (score[v] <= 0)
			{
				goodvar_stack[index] = mypop(goodvar_stack);
				already_in_goodvar_stack[goodvar_stack[index]] = index;
				already_in_goodvar_stack[v] = -1;
			}
		}
		if (if_using_neighbor)
		{
			//add goodvar
			for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
			{
				v = var_neighbor[flipvar][i];
				if (score[v] > 0)
				{
					if (already_in_goodvar_stack[v] == -1)
					{
						already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
						mypush(v, goodvar_stack);
					}
				}
			}
		}
		else
		{
			lit *clause_c;
			int c;
			for (int i = 0; i < var_lit_count[flipvar]; ++i)
			{
				c = var_lit[flipvar][i].clause_num;
				clause_c = clause_lit[c];
				for (lit *p = clause_c; (v = p->var_num) != 0; p++)
				{
					if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
					{
						already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
						mypush(v, goodvar_stack);
					}
				}
			}

			if (already_in_goodvar_stack[flipvar] != 0 && score[flipvar] > 0)
			{
				if (goodvar_stack[already_in_goodvar_stack[flipvar]] == flipvar)
				{
					int tem_v = mypop(goodvar_stack);
					goodvar_stack[already_in_goodvar_stack[flipvar]] = tem_v;
					already_in_goodvar_stack[tem_v] = already_in_goodvar_stack[flipvar];
					already_in_goodvar_stack[flipvar] = -1;
				}
			}
		}
	}
}

void Satlike::update_goodvarstack2(int flipvar)
{
	if (mse21) 
	{
		int v;
		//remove the vars no longer goodvar in goodvar stack
		for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
		{
			v = goodvar_stack[index];
			if (score[v] <= 0)
			{
				goodvar_stack[index] = mypop(goodvar_stack);
				already_in_goodvar_stack[goodvar_stack[index]] = index;
				already_in_goodvar_stack[v] = -1;
			}
		}

		for (int i = 0; i < score_change_stack_fill_pointer; i++)
		{
			int v = score_change_stack[i];
			//cout << "v is " << v << " score change time is " << score_change_time[v] << endl;
			if (!if_score_change[v])
				continue;

			if_score_change[v] = false;

			if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
			{
				already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
				mypush(v, goodvar_stack);
			}
		}

		if (already_in_goodvar_stack[flipvar] != 0 && score[flipvar] > 0)
		{
			if (goodvar_stack[already_in_goodvar_stack[flipvar]] == flipvar)
			{
				int tem_v = mypop(goodvar_stack);
				goodvar_stack[already_in_goodvar_stack[flipvar]] = tem_v;
				already_in_goodvar_stack[tem_v] = already_in_goodvar_stack[flipvar];
				already_in_goodvar_stack[flipvar] = -1;
			}
		}
	}
	else
	{
		if (score[flipvar] > 0 && already_in_goodvar_stack[flipvar] == -1)
		{
			already_in_goodvar_stack[flipvar] = goodvar_stack_fill_pointer;
			mypush(flipvar, goodvar_stack);
		}
		else if (score[flipvar] <= 0 && already_in_goodvar_stack[flipvar] != -1)
		{
			int index = already_in_goodvar_stack[flipvar];
			int last_v = mypop(goodvar_stack);
			goodvar_stack[index] = last_v;
			already_in_goodvar_stack[last_v] = index;
			already_in_goodvar_stack[flipvar] = -1;
		}
		int i, v;
		for (i = 0; i < var_neighbor_count[flipvar]; ++i)
		{
			v = var_neighbor[flipvar][i];
			if (score[v] > 0)
			{
				if (already_in_goodvar_stack[v] == -1)
				{
					already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
					mypush(v, goodvar_stack);
				}
			}
			else if (already_in_goodvar_stack[v] != -1)
			{
				int index = already_in_goodvar_stack[v];
				int last_v = mypop(goodvar_stack);
				goodvar_stack[index] = last_v;
				already_in_goodvar_stack[last_v] = index;
				already_in_goodvar_stack[v] = -1;
			}
		}
	}
}

void Satlike::flip(int flipvar)
{
	if (mse21)
	{
		int i, v, c;
		lit *clause_c;

		score_change_stack_fill_pointer = 0;
		int org_flipvar_score = score[flipvar];
		cur_soln[flipvar] = 1 - cur_soln[flipvar];

		for (i = 0; i < var_lit_count[flipvar]; ++i)
		{
			c = var_lit[flipvar][i].clause_num;
			clause_c = clause_lit[c];

			if (cur_soln[flipvar] == var_lit[flipvar][i].sense)
			{
				++sat_count[c];
				if (sat_count[c] == 2) //sat_count from 1 to 2
				{
					score[sat_var[c]] += clause_weight[c];
				}
				else if (sat_count[c] == 1) // sat_count from 0 to 1
				{
					sat_var[c] = flipvar; //record the only true lit's var
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						score[v] -= clause_weight[c];
					}
					sat(c);
				}
			}
			else // cur_soln[flipvar] != cur_lit.sense
			{
				--sat_count[c];
				if (sat_count[c] == 1) //sat_count from 2 to 1
				{
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] -= clause_weight[c];
							sat_var[c] = v;
							break;
						}
					}
				}
				else if (sat_count[c] == 0) //sat_count from 1 to 0
				{
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						score[v] += clause_weight[c];
					}
					unsat(c);
				} //end else if
			}     //end else
		}

		//update information of flipvar
		score[flipvar] = -org_flipvar_score;
		update_goodvarstack1(flipvar);
	}
	else
	{
		int i, v, c;
		lit *clause_c;

		int org_flipvar_score = score[flipvar];
		cur_soln[flipvar] = 1 - cur_soln[flipvar];

		for (i = 0; i < var_lit_count[flipvar]; ++i)
		{
			c = var_lit[flipvar][i].clause_num;
			clause_c = clause_lit[c];

			if (cur_soln[flipvar] == var_lit[flipvar][i].sense)
			{
				++sat_count[c];
				if (sat_count[c] == 2) //sat_count from 1 to 2
				{
					score[sat_var[c]] += clause_weight[c];
				}
				else if (sat_count[c] == 1) // sat_count from 0 to 1
				{
					sat_var[c] = flipvar; //record the only true lit's var
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						score[v] -= clause_weight[c];
					}
					sat(c);
				}
			}
			else // cur_soln[flipvar] != cur_lit.sense
			{
				--sat_count[c];
				if (sat_count[c] == 1) //sat_count from 2 to 1
				{
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] -= clause_weight[c];
							sat_var[c] = v;
							break;
						}
					}
				}
				else if (sat_count[c] == 0) //sat_count from 1 to 0
				{
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						score[v] += clause_weight[c];
					}
					unsat(c);
				} //end else if
			}     //end else
		}

		//update information of flipvar
		score[flipvar] = -org_flipvar_score;
		update_goodvarstack1(flipvar);
	}
}


void Satlike::flip2(int flipvar)
{
	assert(mse21);

	int i, v, c;
    lit *clause_c;

    score_change_stack_fill_pointer = 0;
    int org_flipvar_score = score[flipvar];
    cur_soln[flipvar] = 1 - cur_soln[flipvar];

    for (i = 0; i < var_lit_count[flipvar]; ++i)
    {
        c = var_lit[flipvar][i].clause_num;
        clause_c = clause_lit[c];

        if (cur_soln[flipvar] == var_lit[flipvar][i].sense)
        {
            ++sat_count[c];
            if (sat_count[c] == 2) //sat_count from 1 to 2
            {
                v = sat_var[c];
                score[v] += clause_weight[c];
                if (score[v] > 0 && score[v] - clause_weight[c] <= 0)
                {
                    score_change_stack[score_change_stack_fill_pointer++] = v;
                    if_score_change[v] = true;
                }
            }
            else if (sat_count[c] == 1) // sat_count from 0 to 1
            {
                sat_var[c] = flipvar; //record the only true lit's var
                for (lit *p = clause_c; (v = p->var_num) != 0; p++)
                {
                    score[v] -= clause_weight[c];
                }
                sat(c);
            }
        }
        else // cur_soln[flipvar] != cur_lit.sense
        {
            --sat_count[c];
            if (sat_count[c] == 1) //sat_count from 2 to 1
            {
                for (lit *p = clause_c; (v = p->var_num) != 0; p++)
                {
                    if (p->sense == cur_soln[v])
                    {
                        score[v] -= clause_weight[c];
                        sat_var[c] = v;
                        break;
                    }
                }
            }
            else if (sat_count[c] == 0) //sat_count from 1 to 0
            {
                for (lit *p = clause_c; (v = p->var_num) != 0; p++)
                {
                    score[v] += clause_weight[c];
                    if (score[v] > 0 && score[v] - clause_weight[c] <= 0)
                    {
                        score_change_stack[score_change_stack_fill_pointer++] = v;
                        if_score_change[v] = true;
                    }
                }
                unsat(c);
            } //end else if
        }     //end else
    }

    //update information of flipvar
    score[flipvar] = -org_flipvar_score;
    update_goodvarstack2(flipvar);
}


void Satlike::print_best_solution()
{
    if (best_soln_feasible == 0)
        return;

    printf("v");
    for (int i = 1; i <= num_vars; i++)
    {
        printf(" ");
        if (best_soln[i] == 0)
            printf("-");
        printf("%d", i);
    }
    printf("\n");
}

bool Satlike::verify_sol()
{
    int c, j, flag;
    long long verify_unsat_weight = 0;

    for (c = 0; c < num_clauses; ++c)
    {
        flag = 0;
        for (j = 0; j < clause_lit_count[c]; ++j)
            if (best_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                flag = 1;
                break;
            }

        if (flag == 0)
        {
            if ((unsigned long long)org_clause_weight[c] == top_clause_weight) //verify hard clauses
            {
                //output the clause unsatisfied by the solution
                cout << "c Error: hard clause " << c << " is not satisfied" << endl;

                cout << "c ";
                for (j = 0; j < clause_lit_count[c]; ++j)
                {
                    if (clause_lit[c][j].sense == 0)
                        cout << "-";
                    cout << clause_lit[c][j].var_num << " ";
                }
                cout << endl;
                cout << "c ";
                for (j = 0; j < clause_lit_count[c]; ++j)
                    cout << best_soln[clause_lit[c][j].var_num] << " ";
                cout << endl;
                return 0;
            }
            else
            {
                verify_unsat_weight += org_clause_weight[c];
            }
        }
    }

    if ((unsigned long long)verify_unsat_weight == opt_unsat_weight)
        return 1;
    else
    {
        cout << "c Error: find opt=" << opt_unsat_weight << ", but verified opt=" << verify_unsat_weight << endl;
    }
    return 0;
}

void Satlike::simple_print()
{
    if (best_soln_feasible == 1)
    {
        if (verify_sol() == 1)
            cout << opt_unsat_weight << '\t' << opt_time << endl;
        else
            cout << "solution is wrong " << endl;
    }
    else
        cout << -1 << '\t' << -1 << endl;
}

inline void Satlike::unsat(int clause)
{
    if ((unsigned long long)org_clause_weight[clause] == top_clause_weight)
    {
        index_in_hardunsat_stack[clause] = hardunsat_stack_fill_pointer;
        mypush(clause, hardunsat_stack);
        hard_unsat_nb++;
    }
    else
    {
        index_in_softunsat_stack[clause] = softunsat_stack_fill_pointer;
        mypush(clause, softunsat_stack);
        soft_unsat_weight += org_clause_weight[clause];
    }
}

inline void Satlike::sat(int clause)
{
    int index, last_unsat_clause;

    if ((unsigned long long)org_clause_weight[clause] == top_clause_weight)
    {
        last_unsat_clause = mypop(hardunsat_stack);
        index = index_in_hardunsat_stack[clause];
        hardunsat_stack[index] = last_unsat_clause;
        index_in_hardunsat_stack[last_unsat_clause] = index;

        hard_unsat_nb--;
    }
    else
    {
        last_unsat_clause = mypop(softunsat_stack);
        index = index_in_softunsat_stack[clause];
        softunsat_stack[index] = last_unsat_clause;
        index_in_softunsat_stack[last_unsat_clause] = index;

        soft_unsat_weight -= org_clause_weight[clause];
    }
}

