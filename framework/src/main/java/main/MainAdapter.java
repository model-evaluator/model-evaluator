package main;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.javers.core.Javers;
import org.javers.core.JaversBuilder;
import org.javers.core.MappingStyle;
import org.javers.core.diff.Diff;
import org.javers.core.diff.ListCompareAlgorithm;
import org.javers.core.diff.changetype.InitialValueChange;
import org.javers.core.diff.changetype.ValueChange;
import org.javers.core.diff.changetype.container.ListChange;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import model.Browser;
import model.BrowsingContext;
import model.ModelDiffState;
import model.Document;
import model.History;
import model.Media;
import model.OriginChange;
import model.Window;
import model.function.Access2Media;
import model.function.AddSandbox;
import model.function.CreateBlob;
import model.function.CreateIframe;
import model.function.DocumentWrite;
import model.function.Event;
import model.function.Function;
import model.function.HistoryPushState;
import model.function.Navigate;
import model.function.Popup;
import model.function.Skip;
import model.url.BlankOrigin;
import model.url.Domain;
import model.url.OpaqueOrigin;
import model.url.Origin;
import model.url.Scheme;
import model.url.StartupOrigin;
import model.url.TupleOrigin;
import model.url.Url;
import util.Labels;

public class MainAdapter {
	
	
	
	public static void main(String[] args) {
		if (args.length > 0) {
			String arg0 = args[0];
			String[] newArgs = new String[args.length - 1]; 
		    System.arraycopy(args, 1, newArgs, 0, args.length - 1);
		    args = newArgs;
			
			if (arg0.equals("modelcheck")) {
				
				try {
					modelChecker(newArgs);
				} catch (IOException e) {
					
					e.printStackTrace();
				}
				
			}else if (arg0.equals("validate")) {
				
				try {
					testCaseExecutor(newArgs);
				} catch (Exception e) {
					e.printStackTrace();
				}
				
			}else {
				System.out.println("Something is wrong in the arguments :: Below are two examples on how to run the framework::");
				System.out.println("1) java -jar target/model*.jar modelcheck M_cam/test.als cameraAttack 100 0 1 \n M_cam/test.als = the model, cameraAttack = the property to be checked, 100 = number of instances to generate, 0 = decompose mode, 1 = decompose threads\n it will create a trace.txt file in the input/ directory which can be used in testcase ");
				System.out.println("2) java -jar target/model*.jar validate input/trace.txt ;; input/trace.txt shows the input trace taken from model checker output");
			}
		}else {
			System.out.println("Something is wrong in the arguments :: Below are two examples on how to run the framework::");
			System.out.println("1) java -jar target/model*.jar modelcheck M_cam/test.als cameraAttack 100 0 1 \n M_cam/test.als = the model, cameraAttack = the property to be checked, 100 = number of instances to generate, 0 = decompose mode, 1 = decompose threads\n it will create a trace.txt file in the input/ directory which can be used in testcase ");
			System.out.println("2) java -jar target/model*.jar validate input/trace.txt ;; input/trace.txt shows the input trace taken from model checker output");
		}
		
	}
	

	public static void modelChecker(String[] args) throws IOException {


			A4Reporter rep = new A4Reporter();

        
        	String filename = "models/" + args[0];
        	
        	String property = args[1];

            // Parse+typecheck the model
            System.out.println("=========== Parsing+Typechecking "+filename+" =============");
            Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

            A4Options options = new A4Options();
            
            int num_instances_to_gen  = Integer.parseInt(args[2]);

            options.solver = A4Options.SatSolver.MiniSatJNI;
            options.decompose_mode = Integer.parseInt(args[3]);
            options.decompose_threads = Integer.parseInt(args[4]);
            
            
            for (Command command : world.getAllCommands()) {
    			
    			if (command.label.equals(property)) {
    				
    				try {
    					System.out.println("============ Command "+command+": ============");
    					
    					long tStart_all = System.currentTimeMillis();
                        long tStart_one = System.currentTimeMillis();

                        long tEnd_one = System.currentTimeMillis();
    					
    	                A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
    	                
    	                Path path = Paths.get("input/trace.txt");
    					
    					Files.write(path, ans.toString().getBytes());
    	                
    	                int num_instances = 0;
    	                if (ans.satisfiable()) {
    	                    
    	                    
    	                    num_instances = 0;
    	                    do {
    	                    	
    	                    	System.out.println(ans);
                                System.out.println("---END INSTANCE---\n");
                                 
                                String fileName = "output/solutions_" + property + "_" + num_instances + ".xml";
                                ans.writeXML(fileName);
                                ans = ans.next();
                                if (num_instances == 0) {
                                  tEnd_one = System.currentTimeMillis();
                                }
                                num_instances++;
    	                    	
    	                    }
    	                    while(ans.satisfiable() && (num_instances_to_gen == 0 || num_instances < num_instances_to_gen));
    	                }else {
    	                	System.out.println(ans);
    	                }
    	                long tEnd_all = System.currentTimeMillis();

                        long tDelta_all = tEnd_all - tStart_all; 
                        long tDelta_one = tEnd_one - tStart_one;

                        double elapsedSeconds_all = tDelta_all / 1000.0;
                        double elapsedSeconds_one = tDelta_one / 1000.0;
                        System.out.println("</command>");
                        System.out.println("Time to gen 1 (min): " + Double.toString(elapsedSeconds_one / 60.0)); 
                        System.out.println("Time to gen " + Integer.toString(num_instances) + " (min): " + Double.toString(elapsedSeconds_all / 60.0 )); 
    				}catch(Err e){

    					e.printStackTrace();
    					
    				}
    				
    				

    			}
    			
    		}
	
	}

	
	
	public static void testCaseExecutor(String[] args) throws IOException, NoSuchMethodException, SecurityException, ClassNotFoundException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		
		long tStart_one = System.currentTimeMillis();
		List<Browser> states = Parser.parse(args[0]);
		int a = 0;
		
		List<ModelDiffState> diffStateList = new ArrayList<ModelDiffState>();
		for (int i = 0; i < states.size(); i++) {

			if (i < states.size() - 1) {

				ModelDiffState diffState = new ModelDiffState();
				Object item1 = states.get(i);
				Object item2 = states.get(i + 1);
				
				diffState.rootBc = states.get(i).function.rootBc;
				diffState.bc = states.get(i).function.bc;
				diffState.party = states.get(i).function.party;
				diffState.event = states.get(i).function.event.name;
						

				Javers javers = JaversBuilder.javers()
						.withListCompareAlgorithm(ListCompareAlgorithm.LEVENSHTEIN_DISTANCE)
						.withMappingStyle(MappingStyle.FIELD).build();

				Diff diff = javers.compare(item1, item2);

				diff.getChangesByType(ListChange.class).forEach(ch ->
					diffState.listChanges.add(ch)
				);
				diff.getChangesByType(InitialValueChange.class).forEach(ch ->
					diffState.initValueChanges.add(ch)
				);

				diff.getChangesByType(ValueChange.class).forEach(ch ->
					diffState.valueChanges.add(ch)
				);
				
				//NOTE javers couldnt find the difference between Origins manually added them
				
				for (BrowsingContext bc : states.get(i).bcs) {
					for (BrowsingContext bc2 : states.get(i+1).bcs) {
						if (bc.name.equals(bc2.name)) {
							if(!bc.origin.equals(bc2.origin)) {
								OriginChange oc = new OriginChange();
								oc.bc = bc;
								oc.initialOrigin = bc.origin;
								oc.changeOrigin = bc2.origin;
								diffState.originChanges.add(oc);
							}
						}
					}
				}

				diffStateList.add(diffState);

				//System.out.println("i=" + i + ". " + diff);
			//	System.out.println("==========================");


			}

		}
		
//		for (DiffState diff : diffStateList) {
////			p.getAffectedLocalId().equals(diffState.focusedWindow.name)
//			
//			
//		}
	
		Interpreter interpreter = new Interpreter(states, diffStateList);
		String result = interpreter.interpret();
		
		System.out.println("Test finished: " + result);
		interpreter.invoker.driver.quit();
		
		long tEnd_one = System.currentTimeMillis();
		long tDelta_one = tEnd_one - tStart_one;
		
		double elapsedSeconds_one = tDelta_one / 1000.0;
		System.out.println("Time to validation 1 (min): " + Double.toString(elapsedSeconds_one / 60.0)); 
		
		
	}
	
	

}
