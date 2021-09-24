package util;

import java.util.*; 
import org.json.JSONException;
import org.json.JSONObject;
import org.json.JSONArray;

import java.lang.reflect.Method;

import model.*; 


public class CodeGenerator {


	private String initialState;

	private ArrayList<String> allStatesInOrder;

	private ArrayList<JSONObject> allTransitions;

	private ArrayList<String> orderOfTransitions;

	public CodeGenerator(String initialState, ArrayList<String> allStatesInOrder, ArrayList<JSONObject> allTransitions){
		
		this.initialState 		= initialState;
		this.allStatesInOrder 	= allStatesInOrder;
		this.allTransitions 	= allTransitions;
		this.orderOfTransitions = new ArrayList<String>();

	}

	public String generate() throws Error {
		
		ArrayList<String> states 			= this.allStatesInOrder;
		ArrayList<JSONObject> transitions 	= this.allTransitions;
		
		for(int i = 0; i < states.size(); i++){
			
			String state 		= states.get(i);
			String transition 	= retrieveTransition(state, transitions);
			if (transition.equals("-1")){

			}else{
				orderOfTransitions.add(transition);
			}

		}

		String html = Labels.SIMPLE_HTML;
		String script = Labels.SCRIPT_START_NEWLINE;


		String initialUrlStr = Invoker.properDataSchemeURL("Hello world!");
		String initialWindow = Invoker.windowOpen(initialUrlStr);

		script += initialWindow;

		Window w = new Window();
		w.url = initialWindow;

		
		try{
			
			for(int i = 0; i < orderOfTransitions.size(); i++){

				String transition = orderOfTransitions.get(i);

				Method method = Invoker.class.getMethod(transition, Window.class);
				w = (Window)method.invoke(null, w);
				script += w.resultingStr;
			}
			script += Labels.SCRIPT_END_NEWLINE;
			html += script;
			html += Labels.END_BODY_HTML;
			System.out.println(html);
			return html;

		}catch(Exception e){
			System.out.println(e);
		}
		
		return "-1";

		
	}

	public static String retrieveTransition(String state, ArrayList<JSONObject> transitions ){
		
		for(int i = 0; i < transitions.size(); i++){
			JSONObject jo = transitions.get(i);
			if (jo.get("win").equals(state)){
				String trans = jo.getString("trans");
				String transition;
				int iend = trans.indexOf("$");
				if (iend != -1) {
					transition = trans.substring(0 , iend);
				}else{
					transition = trans;
				}
				return transition;
			}
		}
		return "-1";
	}




}