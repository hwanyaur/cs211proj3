/*execute.c*/

//
// Project: Execution of queries for SimpleSQL
//
// Yaurie Hwang
// Northwestern University
// CS 211, Winter 2023
//

#include <stdbool.h> // true, false
#include <stdio.h>
#include <stdlib.h>
//
// #include any other system <.h> files?
//

#include "execute.h"
#include <assert.h> // assert
#include <string.h> // strcpy, strcat

#include "analyzer.h"
#include "ast.h"
#include "database.h"
#include "parser.h"
#include "scanner.h"
#include "tokenqueue.h"
#include "util.h"

#include "ctype.h"
#include "resultset.h"

//
// implementation of function(s), both private and public
//

//
// step 6
// filters data using "where" in query
//
void step_six(struct SELECT *select, struct ResultSet *rs,
              struct TableMeta *tablemeta) {
  if (select->where != NULL) { // the where clause exists

    struct EXPR *whr = select->where->expr;
    char *colname = whr->column->name; // name of desired column
    int op = whr->operator;

    for (int count = 0; count <= rs->numCols;
         count++) { // iterating through cols

      // printf("here\n");
      if (strcasecmp(colname, tablemeta->columns[count].name) ==
          0) { // found desired col
        // printf("found, it's %s\n", colname);

        for (int rowcount = rs->numRows; rowcount > 0;
             rowcount--) {                              // iterate through rows
          int type = tablemeta->columns[count].colType; // type of col
          double diff = 0; // checks if difference in values

          if (type == COL_TYPE_INT) {
            int val = resultset_getInt(rs, rowcount,
                                       count + 1); // gets val of row,count
            int val2 = atoi(whr->value);
            diff = val - val2;
          } else if (type == COL_TYPE_REAL) {
            double val = resultset_getReal(rs, rowcount, count + 1);
            double val2 = atof(whr->value);
            diff = val - val2;
          } else if (type == COL_TYPE_STRING) {
            char *val = resultset_getString(rs, rowcount, count + 1);
            char *val2 = whr->value;
            diff = strcasecmp(val, val2); // 0 or 1
            free(val);
            // free(val2);
          }
          // diff = val-val2

          // printf("operator = %d\n", op);

          if ((op == 0) && (diff >= 0)) { // EXPR_LT
            resultset_deleteRow(rs, rowcount);
          } else if ((op == 1) && (diff > 0)) { // EXPR_LTE
            resultset_deleteRow(rs, rowcount);
          } else if ((op == 2) && (diff <= 0)) { // EXPR_GT
            resultset_deleteRow(rs, rowcount);
          }
          if ((op == 3) && (diff < 0)) { // EXPR_GTE
            resultset_deleteRow(rs, rowcount);
          }
          if ((op == 4) && (diff != 0)) { // EXPR_EQUAL
            resultset_deleteRow(rs, rowcount);
          }
          if ((op == 5) && (diff == 0)) { // EXPR_NOT_EQUAL
            resultset_deleteRow(rs, rowcount);
          }
        }
        break; // ends loop to search for columns (since already found)
      }
    }

    // print rs
    // resultset_print(rs);
    //
    free(colname);
  } // if where clause exists
  
}

// 
// step 7
// delete columns that are not in query
//
void step_seven(struct SELECT *select, struct ResultSet *rs,
                struct TableMeta *tablemeta) {
  // loop through meta data array ()
  for (int i = 0; i < tablemeta->numColumns; i++) { // numColumns array

    struct COLUMN *curr = select->columns;

    while (curr != NULL) { // loop through ast data to find col
      if (strcasecmp(curr->name, tablemeta->columns[i].name) == 0) { // exists
        break;
      }
      curr = curr->next;
    }
    if (curr == NULL) { // col doesn't exist
      int pos = resultset_findColumn(rs, 1, tablemeta->name,
                                     tablemeta->columns[i].name);
      resultset_deleteColumn(rs, pos);
    }
  }
  // printf("num of rs cols (step 7) = %d\n", rs->numCols);
  // resultset_print(rs);
}

// 
// step 8
// reorder columns to match query
//
void step_eight(struct SELECT *select, struct ResultSet *rs,
                struct TableMeta *tablemeta) {

  struct COLUMN *curr = select->columns; // ast
  int pos = 1;

  while (curr != NULL) { // loop through cols in ast
    int temp = resultset_findColumn(rs, 1, tablemeta->name, curr->name);
    resultset_moveColumn(rs, temp, pos);

    // printf("moved %s from %d to position %d\n", curr->name, temp, pos);
    // Select Title, ID From Movies where Revenue > 100000000;
    pos++;
    curr = curr->next;
  }
}

// 
// step 9
// applies aggregate functions to columns
//
void step_nine(struct SELECT *select, struct ResultSet *rs,
               struct TableMeta *tablemeta) {
  // select max(station) from Stations where Station < "Middle";
  struct COLUMN *curr2 = select->columns;

  while (curr2 != NULL) {
    //printf("col name = %s\n", curr2->name);
    //printf("func = %d\n", curr2->function);

    if (curr2->function != -1) {
      //printf("function = %d\n", curr2->function);
      int colnum = resultset_findColumn(rs, 1, tablemeta->name, curr2->name);
      resultset_applyFunction(rs, curr2->function, colnum);
    }
    curr2 = curr2->next;
  }
}

// 
// step 10
// apply limit clause
//
void step_ten(struct SELECT *select, struct ResultSet *rs,
              struct TableMeta *tablemeta) {
  if (select->limit != NULL) { // limit exists
    int n = select->limit->N;
    while (rs->numRows > n) {
      resultset_deleteRow(rs, rs->numRows); // deletes last row
      // if ()
    }
  }
}

//
// execute_query
//
// execute a select query, which for now means open the underlying
// .data file and output the first 5 lines.
//
void execute_query(struct Database *db, struct QUERY *query) {
  if (db == NULL)
    panic("db is NULL (execute)");
  if (query == NULL)
    panic("query is NULL (execute)");

  if (query->queryType != SELECT_QUERY) {
    printf("**INTERNAL ERROR: execute() only supports SELECT queries.\n");
    return;
  }

  struct SELECT *select = query->q.select; // alias for less typing:

  //
  // the query has been analyzed and so we know it's correct: the
  // database exists, the table(s) exist, the column(s) exist, etc.
  //

  //
  // (1) we need a pointer to the table meta data, so find it:
  //
  struct TableMeta *tablemeta = NULL;

  for (int t = 0; t < db->numTables; t++) {
    if (icmpStrings(db->tables[t].name, select->table) == 0) // found it:
    {
      tablemeta = &db->tables[t];
      break;
    }
  }

  assert(tablemeta != NULL);

  // step 3 select * from movies2;

  struct ResultSet *rs = resultset_create();

  for (int i = 0; i < tablemeta->numColumns; i++) {

    resultset_insertColumn(rs, i + 1, tablemeta->name,
                           tablemeta->columns[i].name, NO_FUNCTION,
                           tablemeta->columns[i].colType);
  }

  //
  // (2) open the table's data file
  //
  // the table exists within a sub-directory under the executable
  // where the directory has the same name as the database, and with
  // a "TABLE-NAME.data" filename within that sub-directory:
  //
  char path[(2 * DATABASE_MAX_ID_LENGTH) + 10];

  strcpy(path, db->name); // name/name.data
  strcat(path, "/");
  strcat(path, tablemeta->name);
  strcat(path, ".data");

  FILE *datafile = fopen(path, "r");
  if (datafile == NULL) // unable to open:
  {
    printf("**INTERNAL ERROR: table's data file '%s' not found.\n", path);
    panic("execution halted");
    exit(-1);
  }

  //
  // (3) allocate a buffer for input, and start reading the data:
  //
  int dataBufferSize =
      tablemeta->recordSize + 3; // ends with $\n + null terminator
  char *dataBuffer = (char *)malloc(sizeof(char) * dataBufferSize);
  if (dataBuffer == NULL)
    panic("out of memory");

  while (true) { // get all possible data in file, each line
    fgets(dataBuffer, dataBufferSize, datafile);

    if (feof(datafile)) { // end of the data file, we're done
      break;
    }

    char *cp = dataBuffer;
    char *end = NULL;
    int rows = resultset_addRow(rs);

    for (int cols = 0; cols < tablemeta->numColumns;
         cols++) { // iterate through all cols
      if (tablemeta->columns[cols].colType == COL_TYPE_INT) { // integer only
        end = strchr(cp, ' '); // first occurence of space
        *end = '\0';
        int value = atoi(cp);

        resultset_putInt(rs, rows, cols + 1, value); // cols + 1 for col 1 based
        cp = end + 1;
      }

      else if (tablemeta->columns[cols].colType == COL_TYPE_REAL) { // reals
        end = strchr(cp, ' '); // first occurence of space
        *end = '\0';
        double value = atof(cp);

        resultset_putReal(rs, rows, cols + 1, value);
        cp = end + 1;
      }

      else if (tablemeta->columns[cols].colType == COL_TYPE_STRING) { // string
        // end = strchr(cp, ' '); //first occurence of space
        end = cp + 1;
        // cp = end + 1;

        while (*end != *cp) {
          end++;
        }
        *end = '\0';

        resultset_putString(rs, rows, cols + 1, cp + 1);
        cp = end + 2;
      }
    }
    // free(dataBuffer);
    // printf("%s\n", dataBuffer);

    // free(cp);
    // free(end);
  } // end while loop
  fclose(datafile);
  // resultset_print(rs);

  // step 6
  // office hours
  // select * from Movies where ID > 1000;
  // Select * from Movies2 where Revenue > 100000000;
  step_six(select, rs, tablemeta);

  // step 7
  step_seven(select, rs, tablemeta);

  // step 8
  // printf("step8\n");
  step_eight(select, rs, tablemeta);

  // step 9
  // printf("step9\n");
  step_nine(select, rs, tablemeta);

  // step 10
  // printf("step10\n");
  step_ten(select, rs, tablemeta);

  //frees memory of databuffer
  free(dataBuffer);
  //prints final rs
  resultset_print(rs);
  // frees memory of rs
  resultset_destroy(rs);
} // end execute_query

//--leak-check=full
