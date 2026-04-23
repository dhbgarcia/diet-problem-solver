# Dane Henrich B. Garcia
# CMSC 150 : Diet Problem Solver (Project)

library(shiny)
library(shinythemes)
library(bslib)
library(readr)
library(shinydashboard)
library(shinyjs)

nutrientValues = read.csv("FoodInfo.csv", TRUE, ",")

# Set the variables for each data -- much more easy to bind after making variables



# Set the values for the names

# Food names list from the data
foodNamesList = as.list(nutrientValues$Foods)  

# Convert nutrient values to matrix
initial_nutrientValuesMatrix  = as.matrix(nutrientValues) 

# Get column names from matrix
labelnames = colnames(initial_nutrientValuesMatrix ) 

# Third column name for serving size
servinglabel = labelnames[3]  

# Second column name for price
pricelabel = labelnames[2] 

# From 4th to 14th columns, the nutrient names
nutrientnames = labelnames[4:14]  

#-------------------------------------------
#Extracting values to match the name for binding later on

# Extract serving sizes (third column)
servingSizes  = initial_nutrientValuesMatrix [,3]  

# Remove serving sizes column
nutrientDataWithoutServing  = initial_nutrientValuesMatrix [,-3] 

# First column is food names
foodNamesColumn = initial_nutrientValuesMatrix [,1] 

# Remove the first column (food names)
nutrientValuesMatrix  = nutrientDataWithoutServing[,-1]  

# Food costs from the first column of nutrient matrix
foodCosts  = (nutrientValuesMatrix [,1])  

# Remove the cost column
nutrientValuesMatrix  = nutrientValuesMatrix [,-1] 

# Add costs back to the matrix
nutrientValuesMatrix  = cbind(nutrientValuesMatrix , foodCosts )

# Setup the nutrient matrix for further use
setupNutrientMatrix  = nutrientValuesMatrix  

# Change matrix values to numbers
nutrientValuesMatrix = c()  # Reset the matrix

for (i in 1:12) {  # Loop through the columns of nutrient values
  nutrientValuesMatrix = cbind(nutrientValuesMatrix, as.numeric(parse_number(setupNutrientMatrix[, i])))  # Convert each column to number
}

addConstraints = function(nutrientValuesMatrix ) {
  # Create new matrix by binding the original and the negated nutrient column
  newMatrix = cbind(nutrientValuesMatrix [, 1:11], (-1) * nutrientValuesMatrix [, 1:11])
  
  # Add price column from nutrientValuesMatrix 
  newMatrix = cbind(newMatrix, nutrientValuesMatrix [, 12])
  
  # Make nutrient label for the new matrix
  nutrientLabel = c(nutrientnames, nutrientnames, pricelabel)
  
  # Set column names for the new matrix
  colnames(newMatrix) = nutrientLabel
  
  return(newMatrix)
}

# Add constraints to the nutrient values matrix
nutrientValuesMatrix = addConstraints(nutrientValuesMatrix)
locateFoodIndices = function(selectedFoods) {
  # Use match to find indices of selected foods in the foodNamesList list
  foodIndices = match(selectedFoods, foodNamesList)
  
  # Return the vector of indices
  return(foodIndices)
}

#Final Matrix to pass down in the simpelx algo

generateFinalMatrix = function(selectedItems) {
  selected_food_matrix = c()  # Matrix to store nutrient data of selected foods
  
  # Add rows for selected foods from the nutrient matrix
  for (item in selectedItems) {
    selected_food_matrix = cbind(selected_food_matrix, nutrientValuesMatrix [locateFoodIndices(item), ])
  }
  
  # Define the constraint coefficients and cost function
  constraint_values = c(
    2000, 0, 0, 0, 0, 25, 50, 5000, 50, 800, 10, 
    -2250, -300, -65, -2400, -300, -100, -100, -50000, -20000, -1600, -30, 1
  )
  
  # Check if any food is selected
  if (length(selected_food_matrix[1, ]) != 0) {
    # Add the constraint values as the last column
    selected_food_matrix = cbind(selected_food_matrix, constraint_values)
    selected_food_matrix = t(selected_food_matrix)  # Transpose to ensure row alignment
    
    # Adjust the cost row
    selected_food_matrix[nrow(selected_food_matrix), ] = -1 * selected_food_matrix[nrow(selected_food_matrix), ]
    selected_food_matrix[nrow(selected_food_matrix), ncol(selected_food_matrix)] = 0
    
    # Extract the cost column and remove it from the main matrix
    Optimal_Cost = selected_food_matrix[, ncol(selected_food_matrix)]
    selected_food_matrix = selected_food_matrix[, -ncol(selected_food_matrix)]
    
    # Create slack variable matrix (identity matrix for constraints)
    slack_variables = diag(1, nrow = nrow(selected_food_matrix), ncol = nrow(selected_food_matrix))
    colnames(slack_variables) = append(selectedItems, "Cost")
    
    # Create serving constraints matrix
    serving_constraints = diag(-1, nrow = nrow(selected_food_matrix) - 1, ncol = nrow(selected_food_matrix) - 1)
    max_serving_constraints = rep(10, nrow(selected_food_matrix) - 1)
    serving_constraints = rbind(serving_constraints, max_serving_constraints)
    colnames(serving_constraints) = paste(selectedItems, "Servings")
    
    # Combine the food matrix, serving constraints, slack variables, and cost column
    final_matrix = cbind(selected_food_matrix, serving_constraints, slack_variables, Optimal_Cost)
    return(final_matrix)  # Return the final assembled matrix
  }
  
  return(NULL)  # Return NULL if no food is selected
}


Simplex = function(tableau) {
  initial_tableau = tableau
  tableau_list = list()  # List to store tableaux for each iteration
  iteration = 1  # Initialize iteration counter
  
  # Simplex method: Continue until no negative value in the last row
  while (min(tableau[nrow(tableau), -ncol(tableau)]) < 0) {
    # Find the pivot column (most negative value in the last row)
    pivot_col = which.min(tableau[nrow(tableau), -ncol(tableau)])
    
    # Calculate test ratios to determine the pivot row
    test_ratios = tableau[1:(nrow(tableau) - 1), ncol(tableau)] / tableau[1:(nrow(tableau) - 1), pivot_col]
    test_ratios[test_ratios <= 0] = Inf  # Ignore non-positive ratios
    
    # If no valid pivot row, basicSolution is infeasible
    if (all(is.infinite(test_ratios))) {
      print("NO FEASIBLE basicSolution")
      result = list(
        finalTableau = NULL,
        iterations = tableau_list,
        basicbasicSolution = NULL,
        Z = NULL,
        outputSummary = NULL
      )
      return(result)
    }
    
    # Find the pivot row (smallest positive test ratio)
    pivot_row = which.min(test_ratios)
    pivot_element = tableau[pivot_row, pivot_col]
    
    # Normalize the pivot row
    tableau[pivot_row, ] = tableau[pivot_row, ] / pivot_element
    
    # Gauss-Jordan elimination to update other rows
    for (i in 1:nrow(tableau)) {
      if (i != pivot_row) {
        multiplier = tableau[i, pivot_col]
        tableau[i, ] = tableau[i, ] - multiplier * tableau[pivot_row, ]
      }
    }
    
    # Store the updated tableau
    tableau_list[[iteration]] = tableau
    iteration = iteration + 1
  }
  
  # Extract basic basicSolution from the final tableau
  basicSolution = c(tableau[nrow(tableau), -(ncol(tableau)-1)])
  
  # Compute the food summary or the output 
  foodCosts = initial_tableau[1:(nrow(initial_tableau) - 1), ncol(initial_tableau)]
  outputSummary = apply(as.matrix(FoodSummary(basicSolution, foodCosts )), 2, function(x) formatC(x, format = "f", digits = 2))
  outputSummary = cbind(rownames(outputSummary), outputSummary)
  rownames(outputSummary) = NULL
  colnames(outputSummary) = c("Food", "Serving", "Cost($)")
  
  # Compile results into a labeled list
  result = list(
    finalTableau = tableau,
    iterations = tableau_list,
    basicbasicSolution = basicSolution,
    Z = tableau[nrow(tableau), ncol(tableau)],
    outputSummary = outputSummary
  )
  
  print(result)  # Print the result for inspection
  
  return(result)
}


FoodSummary = function(inputVector, priceList) {
  # Define the starting index for relevant data
  constraintOffset = 22 + length(priceList)
  relevantData = inputVector[(constraintOffset + 1):(length(inputVector) - 1)]
  
  # Filter non-zero servings and compute their corresponding price details
  nonZeroData = relevantData[relevantData != 0]
  nonZeroPrices = priceList[relevantData != 0]
  
  # Create the output matrix
  servings = nonZeroData
  prices = nonZeroData * nonZeroPrices
  outputSummary = cbind(servings, prices)
  
  return(outputSummary)
}




ui = dashboardPage(
  dashboardHeader(title = "Mario's Diet Problem Solver"),
  
  dashboardSidebar(
    sidebarMenu(
      menuItem("Home", tabName = "home", icon = icon("home")),
      menuItem("Food Selection", tabName = "foodSelection", icon = icon("utensils")),
      menuItem("Optimization Results", tabName = "optimizationResults", icon = icon("chart-line")),
      menuItem("About the Developer", tabName = "aboutDeveloper", icon = icon("user")),
      menuItem("Instructions", tabName = "instructions", icon = icon("book"))
    )
  ),
  
  dashboardBody(
    useShinyjs(),
    tags$head(
      tags$style(
        HTML('
        body, html {
          height: 100%;
          margin: 0;
          padding: 0;
        }
        .content-wrapper {
          padding: 20px;
          height: calc(100% - 50px);
          overflow-y: auto;
        }
        .box {
          border-radius: 10px;
        }
        .final-tableau {
          height: 400px;
          overflow-y: scroll;
        }
        .iterations-scroll {
          max-height: 300px;
          overflow-y: scroll;
        }

        /* Style to center the buttons and add hover effect */
        .center-buttons {
          text-align: center;
          margin-top: 20px;
        }
        .action-button {
          display: inline-block;
          margin: 5px;
          padding: 10px 20px;
          font-size: 16px;
          border: none;
          border-radius: 5px;
          background-color: #007bff;
          color: white;
          cursor: pointer;
          transition: background-color 0.3s;
        }
        .action-button:hover {
          background-color: #0056b3;
        }
      ')
      )
    ),
    
    tabItems(
      # Home Page Tab
      tabItem(
        tabName = "home",
        fluidRow(
          column(
            width = 12,
            div(
              align = "center",
              tags$img(src = "mario.png", width = "100%")
            )
          )
        )
      ),
      
      
      # Food Selection Tab
      # Food Selection Tab
      tabItem(
        tabName = "foodSelection",
        fluidRow(
          # Adding action buttons in the Food Selection tab
          box(
            title = "Food Selection",
            status = "primary",
            solidHeader = TRUE,
            width = 12,
            column(3, checkboxGroupInput("foodlist", label = NULL, choices = foodNamesList[1:floor(length(foodNamesList)/4)], selected = NULL)),
            column(3, checkboxGroupInput("foodlist", label = NULL, choices = foodNamesList[(floor(length(foodNamesList)/4)+1):(2*floor(length(foodNamesList)/4))], selected = NULL)),
            column(3, checkboxGroupInput("foodlist", label = NULL, choices = foodNamesList[(2*floor(length(foodNamesList)/4)+1):(3*floor(length(foodNamesList)/4))], selected = NULL)),
            column(3, checkboxGroupInput("foodlist", label = NULL, choices = foodNamesList[(3*floor(length(foodNamesList)/4)+1):length(foodNamesList)], selected = NULL)),
            actionButton("select_all", "Check All"),
            actionButton("reset", "Reset"),
            actionButton("submit", "Solve")
          ),
          
          # Food Selection matrix box
          box(
            title = "Selected Foods Initial",
            status = "primary",
            solidHeader = TRUE,
            width = 12,
            style = "height: calc(100vh - 100px); overflow-y: scroll;",  
            tableOutput("matrix_table"),
            collapsible = TRUE,  
            collapsed = TRUE     
          ),
          
          # Simplex result box
          box(
            title = "Simplex Result",
            status = "info",
            solidHeader = TRUE,
            width = 12,
            style = "height: calc(100vh - 100px); overflow-y: scroll;",  
            tableOutput("matrix_simplex"),
            collapsible = TRUE,  
            collapsed = TRUE     
          )
        )
      ),
      
      
      # Optimization Results Tab
      tabItem(
        tabName = "optimizationResults",
        fluidRow(
          box(
            title = "Optimization Results",
            status = "primary",
            solidHeader = TRUE,
            width = 12,
            tabsetPanel(
              tabPanel("Optimal Value Results",
                       textOutput("optimization_result"),
                       br(),
                       tableOutput("matrix_outputSummary")  # Table for servings and cost breakdown
              ),
              
              tabPanel("Basic basicSolution",
                       style = "max-height: 400px; overflow: auto;", 
                       tableOutput("basic_basicSolution_table")
              ),
              tabPanel("Solver Iterations",
                       sliderInput("iterations_slider", 
                                   "Select number of iterations to display", 
                                   min = 1, 
                                   max = 1000,  
                                   value = 5),
                       div(
                         class = "iterations-scroll",  # Scroll for iterations
                         tableOutput("iterations_table")
                       )
              ),
              tabPanel("Final Tableau",  # New tab for final tableau
                       div(
                         class = "final-tableau",  # Scroll for final tableau
                         tableOutput("final_tableau")  # Render final tableau here
                       )
              )
            )
          )
        )
      ),
      
      # About Developer Tab
      tabItem(
        tabName = "aboutDeveloper",
        fluidRow(
          # Directly placing the image without a box
          column(
            width = 12,  # Ensures the image takes up the full width
            align = "center",  # Center the image horizontally
            tags$img(src = "about.png", width = "100%")  # Image source and size
          )
        )
      ),
      
      
      # Instructions Tab
      tabItem(
        tabName = "instructions",
        fluidRow(
          # Directly placing the image without a box
          column(
            width = 12,  # Ensures the image takes up the full width
            align = "center",  # Center the image horizontally
            tags$img(src = "instruct.png", alt = "Instructions", width = "100%")  # Image source and size
          )
        )
      )
      
      
    )
  )
)




server = function(input, output, session) {
  
  selected_foods = reactiveVal(NULL)
  optimized_data = reactiveVal(NULL)  
  simplex_result = reactiveVal(NULL)
  
  # Select all foods button
  observeEvent(input$select_all, {
    updateCheckboxGroupInput(session, "foodlist", selected = foodNamesList)
  })
  
  # Reset button to clear selections and outputs
  observeEvent(input$reset, {
    updateCheckboxGroupInput(session, "foodlist", selected = character(0))
    selected_foods(NULL)
    optimized_data(NULL)  
    
    #Setting them initially as empty
    output$matrix_table = renderTable({ NULL })
    output$matrix_simplex = renderTable({ NULL })
    output$optimized_menu = renderText({ NULL })
  })
  
  # Submit button for optimization
  observeEvent(input$submit, {
    foods = generateFinalMatrix(input$foodlist)
    selected_foods(foods)
    
    if (!is.null(foods)) {
      # Apply Simplex method to get the results
      result = Simplex(foods)
      simplex_result(result)
      
      if (is.list(result)) {
        
        optimized_data(result)
        
        # Displaying the foods matrix
        output$matrix_table = renderTable({
          foods  
        })
        
        # Displaying the simplex result (final tableau)
        output$matrix_simplex = renderTable({
          result$finalTableau  
        })
        
        output$optimization_result = renderText({
          simplex_output = simplex_result()  # Get the reactive value of the Simplex result
          
          if (!is.null(simplex_output$errorMessage)) {
            # If there's an error message (infeasible basicSolution or constraints not met)
            return(simplex_output$errorMessage)
          } else if (!is.null(simplex_output$Z)) {
            # If the optimal basicSolution is found, display the cost
            total_cost = round(simplex_output$Z, 2)
            return(paste("The cost of this optimal diet is $", total_cost, " per day.", sep = ""))
          } else {
            # If no Simplex result, return a message indicating that the basicSolution isn't feasible
            return("   Sorry, no feasible basicSolution found.")
          }
        })
        
        output$matrix_outputSummary = renderTable({
          simplex_output = simplex_result()  # Get the reactive value of the Simplex result
          if (!is.null(simplex_output$finalTableau)) {
            return((simplex_output$outputSummary))  # Render the final tableau from Simplex result
          }
          if(!is.null(selected_foods())){
            infeasible = as.matrix(c(" "))
            colnames(infeasible) = c("It is not possible to meet the nutritional constraints with the foods that you have
selected. The possible reason is that the pivot element is 0.")
            return(infeasible)
          }# If no Simplex result, return nothing
          return(NULL)
        })
        
        # Output the final tableau of the optimization
        output$final_tableau = renderTable({
          simplex_result()$finalTableau
        })
        
        output$basic_basicSolution_table = renderTable({
          simplex_output = simplex_result()  # Get the reactive value of the Simplex result
          
          if (!is.null(simplex_output$errorMessage)) {
            # If there's an error message (infeasible basicSolution or constraints not met)
            infeasible = data.frame("It is not possible to meet the nutritional constraints with the foods that you have
selected. The possible reason is that the pivot element is 0.")
            colnames(infeasible) = c("The problem is infeasible.")
            return(infeasible)
          } else if (!is.null(simplex_output$basicbasicSolution)) {
            # If the basic basicSolution exists, display the rounded table
            basic_basicSolution = round(simplex_output$basicbasicSolution, 4)
            basic_basicSolution_df = data.frame(t(basic_basicSolution))
            colnames(basic_basicSolution_df) = paste("x", 1:length(basic_basicSolution), sep = "")
            return(basic_basicSolution_df)
          } else {
            # If no Simplex result or basic basicSolution, return a message
            return(data.frame("The problem is infeasible." = "It is not possible to meet the nutritional constraints with the foods that you have
selected. The possible reason is that the pivot element is 0."))
          }
        })
        
        
        # Output the iterations as a scrollable table
        output$iterations_table = renderTable({
          iterations = simplex_result()$iterations
          if (length(iterations) > 0) {
            iterations_to_show = iterations[1:min(length(iterations), input$iterations_slider)]
            return(iterations_to_show)
          }
          return(NULL)
        })
      }
    }
  })
}


shinyApp(ui = ui, server = server)
