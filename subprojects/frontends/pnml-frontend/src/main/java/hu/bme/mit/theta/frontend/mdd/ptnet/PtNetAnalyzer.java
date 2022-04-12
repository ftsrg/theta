package hu.bme.mit.theta.frontend.mdd.ptnet;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.google.common.base.Stopwatch;
import com.koloboke.collect.set.hash.HashObjSets;
import fr.lip6.move.pnml.framework.utils.exception.InvalidIDException;
import hu.bme.mit.delta.collections.IntObjCursor;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.delta.mdd.MddVariableDescriptor;
import hu.bme.mit.theta.common.table.BasicTableWriter;
import hu.bme.mit.theta.common.table.TableWriter;
import hu.bme.mit.theta.frontend.petrinet.model.PetriNet;
import hu.bme.mit.theta.frontend.petrinet.model.Place;
import hu.bme.mit.theta.frontend.petrinet.pnml.PetriNetParser;
import hu.bme.mit.theta.frontend.petrinet.pnml.PnmlParseException;
import hu.bme.mit.theta.frontend.mdd.mdd.BfsProvider;
import hu.bme.mit.theta.frontend.mdd.mdd.GeneralizedSaturationProvider;
import hu.bme.mit.theta.frontend.mdd.mdd.SimpleSaturationProvider;

import javax.imageio.ImageIO;
import java.awt.image.BufferedImage;
import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;

public final class PtNetAnalyzer {
	public static enum IterationStrategy {
		BFS, SAT, GSAT
	}
	
	private static final String JAR_NAME = "hu.bme.mit.zeta[.bat]";
	private              TableWriter writer;
	private final        String[] args;
	
	@Parameter(description = "Path of the input model", required = true)
	String modelPath;
	
	@Parameter(names = "--id", description = "Path of the input model")
	String id = "";

	@Parameter(names = "--csv", description = "Path of the CSV file", required = true)
	String csv;
	
	@Parameter(names = "--properties", description = "Print only the properties of the modelPath (no analysis)",
	           help = true)
	boolean propertiesOnly = false;
	
	@Parameter(names = "--header", description = "Print only a header (for benchmarks)", help = true)
	boolean headerOnly = false;
	
	@Parameter(names = "--depgxl", description =
		"Generate GXL representation of (extended) dependency graph for variable ordering in the" +
		" specified file")
	String depGxl;

	@Parameter(names = "--depgxlgsat", description =
		"Generate GXL representation of (extended) dependency graph for variable ordering in the" +
		" specified file")
	String depGxlGsat;

	@Parameter(names = "--depmat",
	           description = "Generate dependency matrix from the model as a CSV file to the specified path")
	String depMat;

	@Parameter(names = "--depmatpng",
	           description = "Generate dependency matrix from the model as a PNG file to the specified path")
	String depMatPng;
	
	@Parameter(names = "--ordering", description = "Path of the input variable ordering")
	String orderingPath;
	
	@Parameter(names = "--algorithm", description = "The state space generation algorithm to use (BFS, Saturation or " +
	                                                "GeneralizedSaturation)")
	IterationStrategy iterationStrategy;
	
	public static void main(String[] args) {
		final PtNetAnalyzer app = new PtNetAnalyzer(args);
		try {
			app.run();
		} catch (Exception e) {
			System.err.println("[ERROR] An unknown error occured.");
			e.printStackTrace();
		}
	}
	
	public PtNetAnalyzer(final String[] args) {
		this.args = args;
	}
	
	private void run() {
		Stopwatch totalTimer = Stopwatch.createStarted();
		
		try {
			JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(args);
			//logger = benchmarkMode ? NullLogger.getInstance() : new ConsoleLogger(logLevel);
		} catch (final ParameterException ex) {
			System.err.println(ex.getMessage());
			ex.usage();
			return;
		}
		
		File csvFile = new File(csv);
		if (!csvFile.exists()) {
			try {
				csvFile.createNewFile();
			} catch (IOException e) {
				System.err.println("[ERROR] Could not create csv CSV file: " + e.getMessage());
				return;
			}
		}
		
		PrintStream csvStream;
		
		try {
			csvStream = new PrintStream(new FileOutputStream(csvFile, true));
			writer = new BasicTableWriter(csvStream, ",", "\"", "\"");
		} catch (FileNotFoundException e) {
			System.err.println("[ERROR] Could not open csv CSV file: " + e.getMessage());
			return;
		}
		
		if (headerOnly) {
			if (propertiesOnly) {
				ModelProperties.printHeader(writer);
				csvStream.close();
			} else if (iterationStrategy != null) {
				printAnalyzeHeader(writer);
			}
			return;
		}
		
		final File pnmlFile = new File(modelPath);
		final List<PetriNet> petriNets;
		try {
			petriNets = PetriNetParser.loadPnml(pnmlFile).parsePTNet();
		} catch (PnmlParseException e) {
			System.err.println("[ERROR] Invalid PNML: " + e.getMessage());
			return;
		} catch (InvalidIDException e) {
			System.err.println("[ERROR] Invalid ID detected: " + e.getMessage());
			return;
		} catch (Exception e) {
			System.err.println("[ERROR] An error occured while loading the modelPath: " + e.getMessage());
			return;
		}

		if (petriNets.isEmpty()) {
			System.err.println("[ERROR] No Petri net found in the PNML document.");
			return;
		}
		
		final List<Place> ordering;
		if (orderingPath == null) {
			System.err.println("[WARNING] No ordering specified, using default order.");
			ordering = new ArrayList<>(petriNets.get(0).getPlaces());
			ordering.sort((p1, p2) -> String.CASE_INSENSITIVE_ORDER.compare(reverseString(p1.getId()),
				reverseString(p2.getId())
			));
		} else {
			try {
				ordering = VariableOrderingFactory.fromFile(orderingPath, petriNets.get(0));
			} catch (IOException e) {
				System.err.println("[ERROR] Error reading ordering file: " + e.getMessage());
				return;
			} catch (Exception e) {
				System.err.println(e.getMessage());
				return;
			}
		}
		
		PtNetSystem system = new PtNetSystem(petriNets.get(0), ordering);
		
		if (depGxl != null) {
			try {
				final File gxlFile = new File(depGxl);
				if (!gxlFile.exists()) {
					gxlFile.createNewFile();
				}
				final PrintStream gxlOutput = new PrintStream(gxlFile);
				
				// TODO: this would be better with the PetriNet file only.
				gxlOutput.print(PtNetDependency2Gxl.toGxl(system, false));
				gxlOutput.close();
			} catch (FileNotFoundException e) {
				System.err.println("[ERROR] Error creating GXL file: " + e.getMessage());
			} catch (IOException e) {
				System.err.println("[ERROR] Error creating GXL file: " + e.getMessage());
			}
		}
		
		if (depGxlGsat != null) {
			try {
				final File gxlFile = new File(depGxlGsat);
				if (!gxlFile.exists()) {
					gxlFile.createNewFile();
				}
				final PrintStream gxlOutput = new PrintStream(gxlFile);
				
				// TODO: this would be better with the PetriNet file only.
				gxlOutput.print(PtNetDependency2Gxl.toGxl(system, true));
				gxlOutput.close();
			} catch (FileNotFoundException e) {
				System.err.println("[ERROR] Error creating GXL file: " + e.getMessage());
			} catch (IOException e) {
				System.err.println("[ERROR] Error creating GXL file: " + e.getMessage());
			}
		}
		
		if (depMat != null) {
			try {
				final File depMatFile = new File(depMat);
				if (!depMatFile.exists()) {
					depMatFile.createNewFile();
				}
				final PrintStream depMatOutput = new PrintStream(depMatFile);
				
				// TODO: this would be better with the PetriNet file only.
				depMatOutput.print(system.printDependencyMatrixCsv());
				depMatOutput.close();
			} catch (FileNotFoundException e) {
				System.err.println("[ERROR] Error creating dependency matrix file: " + e.getMessage());
			} catch (IOException e) {
				System.err.println("[ERROR] Error creating dependency matrix file: " + e.getMessage());
			}
		}
		
		if (depMatPng != null) {
			if (system.getPlaceCount() < 10000 && system.getTransitionCount() < 10000) {
				try {
					final BufferedImage image = system.dependencyMatrixImage(1);
					ImageIO.write(image, "PNG", new File(depMatPng));
				} catch (IOException e) {
					System.err.println("[ERROR] Error creating dependency matrix file: " + e.getMessage());
				}
			} else {
				System.err.println("[WARNING] Skipping image generation because the model size exceeds 10k places or " +
				                   "transitions.");
			}
		}
		
		if (propertiesOnly) {
			new ModelProperties(system, id).printData(writer);
			//return;
		}
		
		if (iterationStrategy != null) {
			MddVariableOrder variableOrder = JavaMddFactory.getDefault()
				.createMddVariableOrder(LatticeDefinition.forSets());
			for (Place p : ordering) {
				variableOrder.createOnTop(MddVariableDescriptor.create(p));
			}
			
			Stopwatch ssgTimer = Stopwatch.createStarted();
			switch (iterationStrategy) {
				// TODO: NODE COUNT IN MDD!!!!
				case BFS: {
					BfsProvider bfs = new BfsProvider(variableOrder);
					
					final MddHandle stateSpace = bfs.compute(system.getInitializer(),
						system.getTransitions(),
						variableOrder.getDefaultSetSignature().getTopVariableHandle()
					);
					
					ssgTimer.stop();
					totalTimer.stop();
					
					printAnalyzeResults(writer,
						variableOrder,
						system,
						stateSpace,
						bfs,
						totalTimer.elapsed(TimeUnit.MICROSECONDS),
						ssgTimer.elapsed(TimeUnit.MICROSECONDS)
					);
				}
				break;
				case SAT: {
					SimpleSaturationProvider ss = new SimpleSaturationProvider(variableOrder);
					
					final MddHandle stateSpace = ss.compute(system.getInitializer(),
						system.getTransitions(),
						variableOrder.getDefaultSetSignature().getTopVariableHandle()
					);
					
					ssgTimer.stop();
					totalTimer.stop();
					
					printAnalyzeResults(writer,
						variableOrder,
						system,
						stateSpace,
						ss,
						totalTimer.elapsed(TimeUnit.MICROSECONDS),
						ssgTimer.elapsed(TimeUnit.MICROSECONDS)
					);
				}
				break;
				case GSAT: {
					GeneralizedSaturationProvider gs = new GeneralizedSaturationProvider(variableOrder);
					
					final MddHandle stateSpace = gs.compute(system.getInitializer(),
						system.getTransitions(),
						variableOrder.getDefaultSetSignature().getTopVariableHandle()
					);
					
					ssgTimer.stop();
					totalTimer.stop();
					
					printAnalyzeResults(writer,
						variableOrder,
						system,
						stateSpace,
						gs,
						totalTimer.elapsed(TimeUnit.MICROSECONDS),
						ssgTimer.elapsed(TimeUnit.MICROSECONDS)
					);
				}
				break;
			}
		}
		
		//System.err.println("This function is not yet available.");
		return;
	}
	
	private static String reverseString(String str) {
		StringBuilder sb = new StringBuilder(str);
		sb.reverse();
		return sb.toString();
	}

	public static class MddNodeCollector {
		public static Set<MddNode> collectNodes(MddHandle root) {
			Set<MddNode> ret = HashObjSets.newUpdatableSet();
			collect(root.getNode(), ret);
			return ret;
		}

		private static void collect(MddNode node, Set<MddNode> result) {
			if (!result.add(node)) {
				return;
			}

			if (!node.isTerminal()) {
				for (IntObjCursor<? extends MddNode> c = node.cursor(); c.moveNext();) {
					collect(c.value(), result);
				}
			}
		}
	}
	
	// TODO: NODE COUNT IN MDD!!!!
	private void printAnalyzeHeader(TableWriter writer) {
		switch (iterationStrategy) {
			case BFS:
				writer.cell("id");
				writer.cell("modelPath");
				writer.cell("modelName");
				writer.cell("stateSpaceSize");
				writer.cell("finalMddSize");
				writer.cell("totalTimeUs");
				writer.cell("ssgTimeUs");
				writer.cell("nodeCount");
				writer.cell("unionCacheSize");
				writer.cell("unionQueryCount");
				writer.cell("unionHitCount");
				writer.cell("relProdCacheSize");
				writer.cell("relProdQueryCount");
				writer.cell("relProdHitCount");
				writer.newRow();
				break;
			case SAT:
			case GSAT:
				writer.cell("id");
				writer.cell("modelPath");
				writer.cell("modelName");
				writer.cell("stateSpaceSize");
				writer.cell("finalMddSize");
				writer.cell("totalTimeUs");
				writer.cell("ssgTimeUs");
				writer.cell("nodeCount");
				writer.cell("unionCacheSize");
				writer.cell("unionQueryCount");
				writer.cell("unionHitCount");
				writer.cell("saturateCacheSize");
				writer.cell("saturateQueryCount");
				writer.cell("saturateHitCount");
				writer.cell("relProdCacheSize");
				writer.cell("relProdQueryCount");
				writer.cell("relProdHitCount");
				writer.cell("saturatedNodeCount");
				writer.newRow();
				break;
		}
	}
	
	private void printAnalyzeResults(
		TableWriter writer,
		MddVariableOrder variableOrder,
		PtNetSystem system,
		MddHandle result,
		GeneralizedSaturationProvider provider,
		long totalTime,
		long ssgTime
	) {
		String id = this.id;
		String modelPath = this.modelPath;
		String modelName = system.getName();

		Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(result);
		long nodeCount = variableOrder.getMddGraph().getUniqueTableSize();

		long unionCacheSize = variableOrder.getDefaultUnionProvider().getCacheSize();
		long unionQueryCount = variableOrder.getDefaultUnionProvider().getQueryCount();
		long unionHitCount = variableOrder.getDefaultUnionProvider().getHitCount();

		long saturateCacheSize = provider.getSaturateCache().getCacheSize();
		long saturateQueryCount = provider.getSaturateCache().getQueryCount();
		long saturateHitCount = provider.getSaturateCache().getHitCount();

		long relProdCacheSize = provider.getSaturateCache().getCacheSize();
		long relProdQueryCount = provider.getSaturateCache().getQueryCount();
		long relProdHitCount = provider.getSaturateCache().getHitCount();

		final Set<MddNode> nodes = MddNodeCollector.collectNodes(result);
		long finalMddSize = nodes.size();

		final Set<MddNode> saturatedNodes = provider.getSaturatedNodes();
		long saturatedNodeCount = saturatedNodes.size() + 2;

		writer.cell(id);
		writer.cell(modelPath);
		writer.cell(modelName);
		writer.cell(stateSpaceSize);
		writer.cell(finalMddSize);
		writer.cell(totalTime);
		writer.cell(ssgTime);
		writer.cell(nodeCount);
		writer.cell(unionCacheSize);
		writer.cell(unionQueryCount);
		writer.cell(unionHitCount);
		writer.cell(saturateCacheSize);
		writer.cell(saturateQueryCount);
		writer.cell(saturateHitCount);
		writer.cell(relProdCacheSize);
		writer.cell(relProdQueryCount);
		writer.cell(relProdHitCount);
		writer.cell(saturatedNodeCount);
		writer.newRow();
	}

	private void printAnalyzeResults(
		TableWriter writer,
		MddVariableOrder variableOrder,
		PtNetSystem system,
		MddHandle result,
		SimpleSaturationProvider provider,
		long totalTime,
		long ssgTime
	) {
		String id = this.id;
		String modelPath = this.modelPath;
		String modelName = system.getName();

		Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(result);
		long nodeCount = variableOrder.getMddGraph().getUniqueTableSize();

		long unionCacheSize = variableOrder.getDefaultUnionProvider().getCacheSize();
		long unionQueryCount = variableOrder.getDefaultUnionProvider().getQueryCount();
		long unionHitCount = variableOrder.getDefaultUnionProvider().getHitCount();

		long saturateCacheSize = provider.getSaturateCache().getCacheSize();
		long saturateQueryCount = provider.getSaturateCache().getQueryCount();
		long saturateHitCount = provider.getSaturateCache().getHitCount();

		long relProdCacheSize = provider.getSaturateCache().getCacheSize();
		long relProdQueryCount = provider.getSaturateCache().getQueryCount();
		long relProdHitCount = provider.getSaturateCache().getHitCount();


		final Set<MddNode> nodes = MddNodeCollector.collectNodes(result);
		long finalMddSize = nodes.size();

		final Set<MddNode> saturatedNodes = provider.getSaturatedNodes();
		long saturatedNodeCount = saturatedNodes.size() + 2;

		writer.cell(id);
		writer.cell(modelPath);
		writer.cell(modelName);
		writer.cell(stateSpaceSize);
		writer.cell(finalMddSize);
		writer.cell(totalTime);
		writer.cell(ssgTime);
		writer.cell(nodeCount);
		writer.cell(unionCacheSize);
		writer.cell(unionQueryCount);
		writer.cell(unionHitCount);
		writer.cell(saturateCacheSize);
		writer.cell(saturateQueryCount);
		writer.cell(saturateHitCount);
		writer.cell(relProdCacheSize);
		writer.cell(relProdQueryCount);
		writer.cell(relProdHitCount);
		writer.cell(saturatedNodeCount);
		writer.newRow();
	}

	private void printAnalyzeResults(
		TableWriter writer,
		MddVariableOrder variableOrder,
		PtNetSystem system,
		MddHandle result,
		BfsProvider provider,
		long totalTime,
		long ssgTime
	) {
		String id = this.id;
		String modelPath = this.modelPath;
		String modelName = system.getName();

		Long stateSpaceSize = MddInterpreter.calculateNonzeroCount(result);
		long nodeCount = variableOrder.getMddGraph().getUniqueTableSize();

		long unionCacheSize = variableOrder.getDefaultUnionProvider().getCacheSize();
		long unionQueryCount = variableOrder.getDefaultUnionProvider().getQueryCount();
		long unionHitCount = variableOrder.getDefaultUnionProvider().getHitCount();

		long relProdCacheSize = provider.getRelProdCache().getCacheSize();
		long relProdQueryCount = provider.getRelProdCache().getQueryCount();
		long relProdHitCount = provider.getRelProdCache().getHitCount();

		final Set<MddNode> nodes = MddNodeCollector.collectNodes(result);
		long finalMddSize = nodes.size();

		writer.cell(id);
		writer.cell(modelPath);
		writer.cell(modelName);
		writer.cell(stateSpaceSize);
		writer.cell(finalMddSize);
		writer.cell(totalTime);
		writer.cell(ssgTime);
		writer.cell(nodeCount);
		writer.cell(unionCacheSize);
		writer.cell(unionQueryCount);
		writer.cell(unionHitCount);
		writer.cell(relProdCacheSize);
		writer.cell(relProdQueryCount);
		writer.cell(relProdHitCount);
		writer.newRow();
	}
}
