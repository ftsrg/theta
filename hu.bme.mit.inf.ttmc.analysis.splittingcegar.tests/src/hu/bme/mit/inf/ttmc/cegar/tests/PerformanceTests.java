package hu.bme.mit.inf.ttmc.cegar.tests;

import java.util.Collection;
import java.util.Map;

import hu.bme.mit.inf.ttmc.cegar.common.ICEGARBuilder;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.ExcelFormatter;
import hu.bme.mit.inf.ttmc.cegar.tests.formatters.IFormatter;

@SuppressWarnings("unused")
public class PerformanceTests {
	private Collection<ICEGARBuilder> configurations; // Configurations
	Map<String, Boolean> models; // Models
	IFormatter formatter = new ExcelFormatter();

	//@Test
	/*
	 * public void simplePerfTest() { configurations = new ArrayList<>(); //
	 * Basic configurations ClusteredCEGARBuilder ccb = new
	 * ClusteredCEGARBuilder().logger(null).visualizer(null).solverManager(
	 * solverManager).basicManager(basicManager); VisibleCEGARBuilder vcb = new
	 * VisibleCEGARBuilder().logger(null).visualizer(null).solverManager(
	 * solverManager).basicManager(basicManager).useCNFTransformation(true);
	 * InterpolatingCEGARBuilder icb = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).solverManager(
	 * solverManager).basicManager(basicManager).useCNFTransformation(true);
	 *
	 *
	 * // Clustered CEGAR configurations configurations.add(ccb.build()); //
	 * Visible CEGAR configurations configurations.add(vcb.build()); //
	 * Interpolated CEGAR configurations
	 * icb.interpolationMethod(InterpolationMethod.Craig)
	 * .collectFromConditions(false).collectFromSpecification(false).
	 * incrementalModelChecking(false); configurations.add(icb.build());
	 * configurations.add(icb.incrementalModelChecking(true).build());
	 * configurations.add(icb.interpolationMethod(InterpolationMethod.Sequence).
	 * build());
	 *
	 * models = new TreeMap<>(); models.put("models/simple/simple1", false);
	 * models.put("models/simple/simple2", true);
	 * models.put("models/simple/simple3", false);
	 * models.put("models/simple/counter", true);
	 * models.put("models/simple/counter_bad", false);
	 * //models.put("models/simple/counter_parametric", true);
	 * models.put("models/simple/boolean1", false);
	 * models.put("models/simple/boolean2", false);
	 * models.put("models/simple/readerswriters", true);
	 * models.put("models/program/loop", true);
	 * models.put("models/program/loop_bad", false);
	 *
	 * run(8); }
	 */

	//@Test
	/*
	 * public void collectorPerfTest() { configurations = new ArrayList<>(); //
	 * Interpolated CEGAR configurations InterpolatingCEGARBuilder icb = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null)
	 * .solverManager(solverManager).basicManager(basicManager);
	 * icb.useCNFTransformation(true).interpolationMethod(InterpolationMethod.
	 * Craig).incrementalModelChecking(true);
	 *
	 * configurations.add(icb.collectFromConditions(false).
	 * collectFromSpecification(false).build());
	 * configurations.add(icb.collectFromConditions(true
	 * ).collectFromSpecification(false).build());
	 * configurations.add(icb.collectFromConditions(false).
	 * collectFromSpecification(true ).build());
	 * configurations.add(icb.collectFromConditions(true
	 * ).collectFromSpecification(true ).build());
	 *
	 * models = new TreeMap<>(); models.put("models/simple/simple1", false);
	 * models.put("models/simple/simple2", true);
	 * models.put("models/simple/simple3", false);
	 * models.put("models/simple/counter", true);
	 * models.put("models/simple/counter_bad", false);
	 * //models.put("models/simple/counter_parametric", true);
	 * models.put("models/simple/boolean1", false);
	 * models.put("models/simple/boolean2", false);
	 * models.put("models/simple/readerswriters", true);
	 * models.put("models/program/loop", true);
	 * models.put("models/program/loop_bad", false);
	 *
	 * run(5); }
	 */

	//@Test
	/*
	 * public void fischerPerfTest() { configurations = new ArrayList<>(); final
	 * InterpolatingCEGARBuilder icb = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).
	 * interpolationMethod(InterpolationMethod.Craig)
	 * .incrementalModelChecking(true)
	 * //.explicitVariable("lock_b0").explicitVariable("lock_b1") // for
	 * fischer3 .explicitVariable("lock") // for fischer2
	 * .useCNFTransformation(true); configurations.add(icb);
	 * //configurations.add(icb.interpolationMethod(InterpolationMethod.Sequence
	 * ));
	 *
	 * models = new TreeMap<>(); models.put("models/fischer/fischer2", true);
	 * models.put("models/fischer/fischer2_bad", false);
	 * models.put("models/fischer/fischer3_bool", true);
	 * models.put("models/fischer/fischer3_bool_bad", false);
	 *
	 * run(1); }
	 */

	//@Test
	/*
	 * public void cernPerfTest() { configurations = new ArrayList<>(); final
	 * InterpolatingCEGARBuilder icb1 = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).
	 * interpolationMethod(InterpolationMethod.Sequence)
	 * .incrementalModelChecking(true).useCNFTransformation(true);
	 *
	 * configurations.add(icb1);
	 *
	 * final InterpolatingCEGARBuilder icb2 = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).
	 * interpolationMethod(InterpolationMethod.Sequence)
	 * .incrementalModelChecking(true).useCNFTransformation(true).
	 * explicitVariable("loc");
	 *
	 * configurations.add(icb2);
	 *
	 * final InterpolatingCEGARBuilder icb3 = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).
	 * interpolationMethod(InterpolationMethod.Craig)
	 * .incrementalModelChecking(true).useCNFTransformation(true);
	 *
	 * configurations.add(icb3);
	 *
	 * final InterpolatingCEGARBuilder icb4 = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).
	 * interpolationMethod(InterpolationMethod.Craig)
	 * .incrementalModelChecking(true).useCNFTransformation(true).
	 * explicitVariable("loc");
	 *
	 * configurations.add(icb4);
	 *
	 * final VisibleCEGARBuilder vcb = new
	 * VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(
	 * true); configurations.add(vcb); //
	 * -------------------------------------------
	 *
	 * models = new TreeMap<>();
	 *
	 * // MODELS: models.put("models/cern/LOCAL_vc1", false);
	 * models.put("models/cern/LOCAL_vc2", false);
	 * models.put("models/cern/REQ_1-1", true);
	 * models.put("models/cern/REQ_1-8_correct_ttmc", true);
	 * models.put("models/cern/REQ_1-8_incorrect_ttmc", false);
	 * models.put("models/cern/REQ_1-9", true);
	 * //models.put("models/cern/REQ_2-3b_correct_ttmc", true);
	 * //////models.put("models/cern/REQ_2-3b_incorrect_ttmc", false);
	 * models.put("models/cern/REQ_3-1", true);
	 * //models.put("models/cern/REQ_3-2", false);
	 * models.put("models/cern/UCPC-1721", true); //
	 * -------------------------------------------
	 *
	 * //runWithTimeOut(30*60);
	 *
	 * // Run once run(1); }
	 */

	/*
	 * @Test
	 * 
	 * public void hardwarePerfTest() { configurations = new ArrayList<>();
	 * final InterpolatingCEGARBuilder icb1 = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).
	 * interpolationMethod(InterpolationMethod.Sequence)
	 * .incrementalModelChecking(true).useCNFTransformation(true); final
	 * InterpolatingCEGARBuilder icb2 = new
	 * InterpolatingCEGARBuilder().logger(null).visualizer(null).
	 * incrementalModelChecking(true)
	 * .useCNFTransformation(true).interpolationMethod(InterpolationMethod.Craig
	 * ); final VisibleCEGARBuilder vcb = new
	 * VisibleCEGARBuilder().logger(null).visualizer(null).useCNFTransformation(
	 * true);
	 *
	 * // CONFIGURATIONS: configurations.add(icb1); configurations.add(icb2);
	 * configurations.add(vcb);
	 *
	 * models = new TreeMap<>();
	 *
	 * // MODELS: //models.put("models/hardware/ringp0", false);
	 * //models.put("models/hardware/ringp0neg", false);
	 * //models.put("models/hardware/shortp0", false);
	 * //models.put("models/hardware/shortp0neg", false);
	 * //models.put("models/hardware/srg5ptimo", false);
	 * //models.put("models/hardware/srg5ptimoneg", false);
	 * //models.put("models/hardware/srg5ptimonegnv", false);
	 * //models.put("models/hardware/nusmv.syncarb52.B", true);
	 * //models.put("models/hardware/nusmv.syncarb102.B", true);
	 * //models.put("models/hardware/vis.4-arbit1.E", true);
	 * //models.put("models/hardware/vis.emodel.E", true);
	 * //models.put("models/hardware/mutexp0", false);
	 * //models.put("models/hardware/mutexp0neg", false);
	 * //models.put("models/hardware/pdtpmsarbiter", true); //
	 * -------------------------------------------
	 *
	 * runWithTimeOut(5 * 60);
	 *
	 * // Run //run(3); }
	 */

	/*
	 * private void run(final int runs) { // Loop through models final
	 * Map<String, Map<String, CEGARResult[]>> results = new HashMap<>(); for
	 * (final String modelName : models.keySet()) { System.out.println(
	 * "Running model " + modelName); results.put(modelName, new HashMap<>());
	 * // Load final SystemSpecification sysSpec =
	 * SystemSpecificationParser.getInstance().load(modelName + ".system"); //
	 * Loop through configurations for (final ICEGARBuilder builder :
	 * configurations) { ConstraintManager manager = new Z3ConstraintManager();
	 * builder.basicManager(manager).solverManager(manager); ICEGARLoop cegar =
	 * builder.build(); System.out.println("\t" + cegar); // Clone the model
	 * (the algorithm may modify it, e.g. CNF transformation) // Run the
	 * algorithm results.get(modelName).put(cegar.toString(), new
	 * CEGARResult[runs]);
	 * 
	 * for (int i = 0; i < runs; ++i) { manager = new Z3ConstraintManager();
	 * builder.basicManager(manager).solverManager(manager); cegar =
	 * builder.build(); results.get(modelName).get(cegar.toString())[i] =
	 * cegar.check(EcoreUtil.copy(sysSpec).getPropertyDeclarations().get(0)); }
	 * } }
	 * 
	 * System.out.println(); System.out.println("RESULTS:");
	 * System.out.println();
	 * 
	 * // Table with time, iteratons and states formatter.cell(""); for (final
	 * ICEGARBuilder cegar : configurations) formatter.cell(cegar.build() + "",
	 * 3); formatter.newRow(); formatter.cell(""); for (int i = 0; i <
	 * configurations.size(); ++i) { formatter.cell("T"); formatter.cell("#R");
	 * formatter.cell("#S"); } formatter.newRow(); for (final String modelName :
	 * models.keySet()) { formatter.cell((models.get(modelName) ? "$+$ " :
	 * "$-$ ") + modelName.substring(modelName.lastIndexOf('/') + 1)); for
	 * (final ICEGARBuilder cegar : configurations) { final CEGARResult[] result
	 * = results.get(modelName).get(cegar.build().toString()); if
	 * (result[0].specificationHolds() == models.get(modelName)) { float avgTime
	 * = 0; for (int i = 0; i < runs; ++i) avgTime +=
	 * result[i].getElapsedMillis(); avgTime /= runs;
	 * formatter.cell(String.format(Locale.ENGLISH, "%.0f", avgTime));
	 * formatter.cell(result[0].getRefinementCount() + "");
	 * formatter.cell(result[0].getStateSpaceSize() + ""); } else {
	 * formatter.cell("ERR", 3); } } formatter.newRow(); }
	 * 
	 * // Table with step percentages formatter.cell(""); for (final
	 * ICEGARBuilder cegar : configurations) formatter.cell(cegar.build() + "",
	 * 4); formatter.newRow(); formatter.cell(""); for (int i = 0; i <
	 * configurations.size(); ++i) { formatter.cell("In"); formatter.cell("Ch");
	 * formatter.cell("Co"); formatter.cell("Re"); } formatter.newRow(); for
	 * (final String modelName : models.keySet()) {
	 * formatter.cell((models.get(modelName) ? "$+$ " : "$-$ ") +
	 * modelName.substring(modelName.lastIndexOf('/') + 1)); for (final
	 * ICEGARBuilder cegar : configurations) { final CEGARResult result =
	 * results.get(modelName).get(cegar.build().toString())[0]; if
	 * (result.specificationHolds() == models.get(modelName)) {
	 * formatter.cell(String.format(Locale.ENGLISH, "%4.1f",
	 * result.getDetailedTime().get("Initializer") / (float)
	 * result.getElapsedMillis() * 100) + "% "); formatter.cell(
	 * String.format(Locale.ENGLISH, "%4.1f",
	 * result.getDetailedTime().get("Checker") / (float)
	 * result.getElapsedMillis() * 100) + "% ");
	 * formatter.cell(String.format(Locale.ENGLISH, "%4.1f",
	 * result.getDetailedTime().get("Concretizer") / (float)
	 * result.getElapsedMillis() * 100) + "% "); formatter.cell(
	 * String.format(Locale.ENGLISH, "%4.1f",
	 * result.getDetailedTime().get("Refiner") / (float)
	 * result.getElapsedMillis() * 100) + "% "); } else { formatter.cell("ERR",
	 * 4); } } formatter.newRow(); } }
	 * 
	 * private void runWithTimeOut(final int timeout) { formatter.cell(""); for
	 * (final ICEGARBuilder cegar : configurations) formatter.cell(cegar.build()
	 * + "", 3); formatter.newRow(); formatter.cell(""); for (int i = 0; i <
	 * configurations.size(); ++i) { formatter.cell("T"); formatter.cell("#R");
	 * formatter.cell("#S"); } formatter.newRow(); // Loop through models for
	 * (final String modelName : models.keySet()) {
	 * formatter.cell((models.get(modelName) ? "$+$ " : "$-$ ") +
	 * modelName.substring(modelName.lastIndexOf('/') + 1)); // Load final
	 * SystemSpecification sysSpec =
	 * SystemSpecificationParser.getInstance().load(modelName + ".system"); //
	 * Loop through configurations for (final ICEGARBuilder builder :
	 * configurations) { final ConstraintManager manager = new
	 * Z3ConstraintManager();
	 * builder.basicManager(manager).solverManager(manager); final ICEGARLoop
	 * cegar = builder.build(); // Clone the model (the algorithm may modify it,
	 * e.g. CNF transformation) final PropertyDeclaration problem =
	 * EcoreUtil.copy(sysSpec).getPropertyDeclarations().get(0); final
	 * CEGARRunner runner = new CEGARRunner(cegar, problem); runner.start();
	 * 
	 * try { runner.join(timeout * 1000); cegar.stop(); runner.join(); if
	 * (runner.getResult() == null) { formatter.cell("TO", 3); } else { final
	 * CEGARResult result = runner.getResult(); //if
	 * (result.specificationHolds() == models.get(modelName)) {
	 * formatter.cell(result.getElapsedMillis() + "");
	 * formatter.cell(result.getRefinementCount() + "");
	 * formatter.cell(result.getStateSpaceSize() + ""); //} else { //
	 * formatter.cell("ERR", 3); //} } } catch (final InterruptedException e) {
	 * formatter.cell("INT", 3); } } formatter.newRow(); } }
	 * 
	 * static class CEGARRunner extends Thread { private final ICEGARLoop cegar;
	 * private final PropertyDeclaration problem; private volatile CEGARResult
	 * result;
	 * 
	 * public CEGARRunner(final ICEGARLoop cegar, final PropertyDeclaration
	 * problem) { this.cegar = cegar; this.problem = problem; this.result =
	 * null; }
	 * 
	 * @Override public void run() { result = cegar.check(problem); }
	 * 
	 * public CEGARResult getResult() { return result; }
	 * 
	 * }
	 */
}
