# Multi-product
This package makes it possible to create a product of any number of models. That is done by creating the combination of 2 models, than recursively combining the result with the next model.

## Usage
Products should be created by using the `MultiBuilder` class.

You can find examples in the test folder of the package.
## Order of product creation
The stepping order of the model is defined by a function on each composition level, so the order in which 
the models are added to the product should be set keeping that in mind.

Let's say for example we want to create the product of three models A, B and C and want them to take action in the following way:</br>
A &rarr; B &rarr; A &rarr; C &rarr; A &rarr; B &rarr; A &rarr; C....

The recommended order in that case would be to first create the product of B and C, and combine the result with A.
This keeps the functions defining the next stepping model clean: just use `NextSideFunctions#alternating` twice.