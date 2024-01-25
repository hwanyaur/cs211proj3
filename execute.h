/*execute.h*/

//
// Project: Execution of queries for SimpleSQL
//
// Yaurie Hwang
// Northwestern University
// CS 211, Winter 2023
//

#pragma once
#include "database.h"
#include "ast.h"

//
// function declarations:
//

void execute_query(struct Database* db, struct QUERY* query); 
