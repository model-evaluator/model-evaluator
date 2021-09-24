package trans;

import java.net.MalformedURLException;
import java.util.ArrayList;

import org.json.JSONArray;
import org.json.JSONObject;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import exec.TestExecutor;
import util.CodeGenerator;
import util.Labels;
import util.Parser;

public class RunAlloy {
	
	public static void executeAlloyModel(String fileName, String property) throws Err, MalformedURLException {
		
		CompModule world = null;
		try {
            world = CompUtil.parseEverything_fromFile(null, null, fileName);
            //System.out.println(world);
        } catch (Err e) {
            System.err.println("Load failed at " + e.pos);
            System.exit(1);
        }
		A4Options options = new A4Options();
		options.solver = A4Options.SatSolver.SAT4J;
		
		boolean foundProp = false;
		
		for (Command command : world.getAllCommands()) {
			
			if (command.label.equals(property)) {
				foundProp = true;
				A4Solution ans = TranslateAlloyToKodkod.execute_command(null, world.getAllReachableSigs(), command, options);
				String lines[] = ans.toString().split(Labels.LINE_SPLITTER);
				
				JSONObject jo = Parser.retrieveOrdTransition(lines);
				System.out.println(jo.toString());

                String initialState = jo.getString(Labels.FIRST);

                JSONArray jOrdArray = jo.getJSONArray(Labels.ORDER);
                JSONArray jTransitionArray = jo.getJSONArray(Labels.TRANSITION);

                ArrayList<String> listofAllStates = new ArrayList<String>();   
                ArrayList<JSONObject> listofAllTransitions = new ArrayList<JSONObject>(); 

                for (int i=0; i < jOrdArray.length(); i++){ 
                    listofAllStates.add(jOrdArray.getString(i));
                }

                for (int i=0; i < jTransitionArray.length(); i++){ 
                    listofAllTransitions.add(jTransitionArray.getJSONObject(i));
                }

                CodeGenerator cg = new CodeGenerator(initialState, listofAllStates, listofAllTransitions );
                cg.generate();


                
                // if (g != "-1") {
                	
                // 	TestExecutor.executeSample();
                	
                	
                	
                // }else {
                // 	System.err.println("Parser has returned with error");
                //     System.exit(1);
                // }
			}
			
		}
		if (! foundProp) {
            System.err.println("Property "+property+" not found.");
            System.exit(1);
        }
	}

}
