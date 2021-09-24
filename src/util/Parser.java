
package util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.json.JSONObject; 



public class Parser {

	public Parser(){
		
	}


	public static String readXML (String filename){

        try{

            File xmlFile = new File(filename); 
            Reader fileReader = new FileReader(xmlFile); 
            BufferedReader bufReader = new BufferedReader(fileReader); 
            StringBuilder sb = new StringBuilder(); 
            String line = bufReader.readLine(); 
            while( line != null){ 
                sb.append(line).append(Labels.NEW_LINE); 
                line = bufReader.readLine(); 
            } 
            String xml2String = sb.toString(); 
            // System.out.println("XML to String using BufferedReader : "); 
            // System.out.println(xml2String); 
            bufReader.close();
            return xml2String;

        }catch (Exception e){

        }

        return null;

    }

    public static JSONObject retrieveOrdTransition(String ansLines[]){

        JSONObject jo = new JSONObject();

        for(String ansLine : ansLines){
            String line[] = ansLine.split(Labels.EQUALS);
            if (line.length == 2){
                String left     = line[0];
                String right    = line[1];
                right = cleanBrackets(right);

                String leftPattern[] = left.split(Labels.LESS_COLON);

                if (leftPattern.length == 2){

                    String sig          = leftPattern[0];
                    String sig_field    = leftPattern[1];

                    if (sig.equals(Labels.ORDERING_ORD)){
                        if (sig_field.equals(Labels.FIRST_F_CAPITAL)){

                            String order[] = splitDomainSig(right);

                            // orderingDom = order[0];
                            String orderingSig = order[1];

                            jo.put(Labels.FIRST, orderingSig );

                        }else if (sig_field.equals(Labels.NEXT)){

                            Pattern rightPattern = Pattern.compile(Labels.RIGHT_SIDE_PATTERN);
                            Matcher rightMatcher = rightPattern.matcher(right);

                            ArrayList<String> ar = new ArrayList<String>();
                            while (rightMatcher.find()) {
                                
                                String str = rightMatcher.group(1);
                                String order[] = splitDomainSig(str);

                                if (ar.size()>0){

                                    if (order[1].equals(ar.get(ar.size()-1))){
                                        ar.add(order[2]);
                                    }

                                }else{
                                    ar.add(order[1]);
                                    ar.add(order[2]);
                                }

                            }

                            jo.put(Labels.ORDER, ar);

                        }
                    }else if (sig.equals(Labels.WINDOW_TRANSITION)){
                        if (sig_field.equals(Labels.VALUE)){

                            Pattern rightPattern = Pattern.compile(Labels.RIGHT_SIDE_PATTERN);//([^, ]+)
                            Matcher rightMatcher = rightPattern.matcher(right);

                            ArrayList<JSONObject> ar = new ArrayList<JSONObject>();

                            while (rightMatcher.find()) {

                                String str = rightMatcher.group(1);
                                String order[] = splitDomainSig(str);

                                JSONObject jo1 = new JSONObject();
                                jo1.put(Labels.WIN, order[1]);
                                jo1.put(Labels.TRANS, order[2]);
                                System.out.println( order[2]);
                                ar.add(jo1);

                            }

                            jo.put(Labels.TRANSITION, ar);

                        }

                    }
                }

                

            }else{
                System.out.println("A wrong state received");
            }
        }
        return jo;

    }

    public static String cleanBrackets(String str ){

        str = str.substring(str.indexOf(Labels.LEFT_BRACE) + 1);
        str = str.substring(0, str.indexOf(Labels.RIGHT_BRACE));
        return str;

    }
    public static String[] splitDomainSig(String str){
        return str.split(Labels.DASH_GREATER);
    }






}