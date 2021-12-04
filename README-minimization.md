# Minimizing Sequents to Find Modeling Errors in KeYmaera X
### Project by Ben Gafford & Myra Dotzel


### Build instructions
- Build instructions are the same as for the original KeYmaera X release repository
  - BUT: I updated the `keymaera-core/build.sbt` file, and I found that I had to get rid of my IntelliJ cached project data in order to get the `monix` library dependency to import correctly
- `sbt clean assembly` to create the keymaerax.jar file, and this can be run like normal. 
  - minSequents will be printed to the console as they are found using minAuto and minQE. 

### Running instructions
Unfortunately, we did not have time to forward proof tree analysis information to the UI. Instead, we have chosen to 

- We had hoped to push the unused facts through the REST API to the web interface, but that seemed like a low priority thing and we ran out of time
- You can use minQE/minAuto/minAutoXtreme by searching for them in the webui, but you cannot interact with the proof tree analyzer through the webUI currently. 
- To test our tool on your own models, you can copy in your own file to a new test (following the format of "Aerodynamic Bouncing Ball: nonoverlapping domain constraints"). This can be a model with or without a stored tactic 
- Disclaimers: 
  - There are some uncaught exceptions / assertion failures that come from the timeout wackiness
### High-level implementation
Perhaps expectedly, this was way harder to implement than expected.

Most of the code is in `MinimizationLibrary.scala`. 
I didn't do anything bad to the correctness-critical kernel. 
Some code is scattered throughout to carry necessary data, as outlined below. 
We didn't have any familiarity with Scala before this, so we probably didn't follow conventions everywhere.

#### Supporting minimum sequent
- Added fields and modified functions of ElidingProvable to support carrying a `minSequent` similar to a `proved` field 
- Modified Lemmas and Lemma storage to optionally store the minimum sequent that was used to prove the conclusion

#### Minimizing proof tactics
- Timeouts implemented using the `monix` library, which seemed like the best/easiest way given the time constraints. This library permits Tasks which are cancelable. 
- Valid mutations are determined by using the ExpressionTraversal class to extract and substitute formulas into other formulas
- Valid mutations depend on whether minQE or minAuto is being used
- We attempt a proof on all valid mutations -- this is bad, but easier to implement than storing metadata about valid substitutions 
- Since we store no metadata about which mutation is the "best", we count tokens to understand which formula is weaker. Since all of our mutations are weakenings that reduce the number of tokens, it is necessarily true that formulas derived from our mutations with fewer tokens are weaker. 
- We scrape program constraints out of programs, and use these as a proxy for what is weaker. 
- 
#### Proof tree analysis
- Added tree member functions to compute allWitnessedFacts, allUsedFacts, and allUnusedFacts 

#### Testing & Validation Methodology
- Tests can be found in MinAutoTests.scala and WitnessedFactsTests.scala
- Tried a property-based testing approach to validate that candidate weakenings are weaker than the original sequents, using the RandomFormula as test generation
  - This wasn't the most interesting thing, but helped to identify a lot of parsing errors
- Include many manual examples of correct usage of the tool
- Most tests don't have meaningful labels, but most are small and self-evident
