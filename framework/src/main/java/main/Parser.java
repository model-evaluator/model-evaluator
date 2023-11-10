package main;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
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

import com.google.gson.JsonObject;
import com.google.gson.JsonPrimitive;

import model.Browser;
import model.BrowsingContext;
import model.DiffState;
import model.Document;
import model.History;
import model.Media;
import model.Window;
import model.function.Access2Media;
import model.function.AddSandbox;
import model.function.CreateBlob;
import model.function.CreateIframe;
import model.function.DocumentWrite;
import model.function.Event;
import model.function.Function;
import model.function.HistoryPushState;
import model.function.LocationReplace;
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

public class Parser {
	
	public Parser () {
		
	}
	
	public static List<Browser> parse(String file) throws IOException {
		FileInputStream fstream = new FileInputStream(file);
		BufferedReader br = new BufferedReader(new InputStreamReader(fstream));

		String strLine;
		
		strLine = br.readLine();
		
		if (strLine.equals(Labels.INSTANCE)) {
			strLine = br.readLine();
			
			String ansLine[] = strLine.split(Labels.EQUALS);
			if(ansLine.length == 2 && ansLine[0].equals(Labels.LOOP)) {
				JsonObject[] rawStates = new JsonObject[Integer.parseInt(ansLine[1])+1];
				Pattern p = Pattern.compile("------State ");
				Matcher m;
				int stateNum = 0;
				while ((strLine = br.readLine()) != null) {
					
					m = p.matcher(strLine);
					if(m.find()) {
						break;
					}
				}
				
				rawStates[stateNum] = new JsonObject();
				while ((strLine = br.readLine()) != null) {
					
					m = p.matcher(strLine);
					if(m.find()) {
						stateNum++;
						rawStates[stateNum] = new JsonObject();
					}else {
						
						
						strLine = strLine.replace("{", "");
						strLine = strLine.replace("}", "");
						
						ansLine = strLine.split(Labels.EQUALS);
						if (ansLine.length  == 2) {
							
							rawStates[stateNum].addProperty(ansLine[0], ansLine[1]);
						}
						
						
					}
				}
				
				List<Browser> states = new ArrayList<Browser>();
				
				try {
					
					for(int i = 0; i < rawStates.length; i++) {
						JsonObject rawState = rawStates[i];
						Browser browser = new Browser();
						
						browser.urls = findListOfUrls(rawState);
						
						browser.medias = findListOfMedia(rawState, browser);
						
						
						
						
						JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/Browser<:bcs");
						
						ansLine = jsA.toString().split(",");
						for (String line : ansLine) {
							p = Pattern.compile("(.*)/(BrowsingContext\\$[0-9])");
						    m = p.matcher(line);
						    if(m.find()) {
						    	
						    	String bcName = m.group(2).toString();
						    	
						    	BrowsingContext bc = findBcInBcs(bcName, browser);
						    	
						    	if (bc == null) {
						    		bc = assignBrowsingContext(bcName, rawState, browser);
						    		
						    		browser.bcs.add(bc);
						    	}
						    	
						    	
						    }
							
						}
						browser.function = findFunction(rawState, browser);
						states.add(browser);
						
					}
					int xx = 0;
					
					return states;
					
					

					
				}catch(Exception e) {
					
					e.printStackTrace();
					
				}finally {
					fstream.close();
				}
				
				
				
				

			}
		}
		return null;
		
	}
	
	public static Function findFunction(JsonObject rawState, Browser browser) throws ClassNotFoundException, NoSuchMethodException, SecurityException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, NoSuchFieldException {
		
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/Function");
		
		Function f = new Function();
		
		Pattern p = Pattern.compile("(.*)/(Navigate|Popup|HistoryPushState|CreateBlob|CreateIframe|AddSandbox|DocumentWrite|Access2Media|Skip)(\\$[0-9])");
		Matcher m = p.matcher(jsA.toString());
		if(m.find()) {
			String evName = m.group(2).toString();
			
//			Class<?> clazz = Class.forName("model.function.Event");
//			for (Object enumConstant : clazz.getEnumConstants()) {
//		        
//		        if(enumConstant.toString().equals(evName)) {
//		        	f.event = (Event1) enumConstant;
//		        }
//		    }
			
			Event event;
			
			
			if (evName.equals("Navigate")) {
				boolean lr = findLocationReplace(rawState);
				if (lr) {
					evName = "LocationReplace";
					event = new LocationReplace();
				}else {
					event = new Navigate();
				}
				
				String urlText = findFunctionUrl("Navigate<:url", rawState);
				event.getClass().getDeclaredField("url").set(event, urlText);
				String responseText = findFunctionProperty("Navigate<:response", "(.*)/(Document)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("response").set(event, responseText);
				String xFrameOption = findXFrameOptions(responseText, rawState);
				event.getClass().getDeclaredField("xFrameOption").set(event, xFrameOption);
				
				
			}else if (evName.equals("CreateBlob")) {
				event = new CreateBlob();
				String urlText = findFunctionUrl("CreateBlob<:url", rawState);
				event.getClass().getDeclaredField("url").set(event, urlText);
				
			}else if(evName.equals("HistoryPushState")) {
				event = new HistoryPushState();
				String urlText = findFunctionUrl("HistoryPushState<:url", rawState);
				event.getClass().getDeclaredField("url").set(event, urlText);
				String tarUrlText = findFunctionUrl("HistoryPushState<:tarUrl", rawState);
				event.getClass().getDeclaredField("tarUrl").set(event, tarUrlText);
				
				
			}else if(evName.equals("CreateIframe")) {
				event = new CreateIframe();
				String urlText = findFunctionUrl("CreateIframe<:url", rawState);
				event.getClass().getDeclaredField("url").set(event, urlText);
				String responseText = findFunctionProperty("CreateIframe<:response", "(.*)/(Document)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("response").set(event, responseText);
				String newBcText = findFunctionProperty("CreateIframe<:newBc", "(.*)/(BrowsingContext)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("newBc").set(event, newBcText);
				
				
			}else if(evName.equals("DocumentWrite")) {
				event = new DocumentWrite();
				String newElText = findFunctionProperty("DocumentWrite<:newEl", "(.*)/(Document)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("newEl").set(event, newElText);
				String targetBcText = findFunctionProperty("DocumentWrite<:targetBc", "(.*)/(BrowsingContext)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("targetBc").set(event, targetBcText);
				
			}else if(evName.equals("Popup")) {
				event = new Popup();
				String urlText = findFunctionUrl("Popup<:url", rawState);
				event.getClass().getDeclaredField("url").set(event, urlText);
				String responseText = findFunctionProperty("Popup<:response", "(.*)/(Document)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("response").set(event, responseText);
				String newBcText = findFunctionProperty("Popup<:newBc", "(.*)/(BrowsingContext)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("newBc").set(event, newBcText);
				
				
			}else if(evName.equals("AddSandbox")) {
				event = new AddSandbox();
				String sandBcText = findFunctionProperty("AddSandbox<:sandBc", "(.*)/(BrowsingContext)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("sandBc").set(event, sandBcText);
				
			}else if(evName.equals("Access2Media")) {
				event = new Access2Media();
				String mediaText = findFunctionProperty("Access2Media<:media", "(.*)/(Media)(\\$[0-9])", rawState );
				event.getClass().getDeclaredField("media").set(event, mediaText);
				
				
			}else {
				event = new Skip();
				
			}
			event.name = evName;
			f.event = event; 
			
			
			jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/Function<:rootBc");
			p = Pattern.compile("(.*)/(BrowsingContext\\$[0-9])");
			m = p.matcher(jsA.toString());
			if (m.find()) {
				f.rootBc = m.group(2).toString();
			}
			
			jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/Function<:bc");
			p = Pattern.compile("(.*)/(BrowsingContext\\$[0-9])");
			m = p.matcher(jsA.toString());
			if (m.find()) {
				f.bc = m.group(2).toString();
			}
			
			jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/Function<:party");
			p = Pattern.compile("(.*)/(BrowsingContext\\$[0-9])");
			m = p.matcher(jsA.toString());
			if (m.find()) {
				f.party = m.group(2).toString();
			}
			
			
		}
		
		
		
		
		
		return f;
	}
	
	public static boolean findLocationReplace (JsonObject rawState) {
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/Navigate<:lr");
		Pattern p = Pattern.compile("(.*)/(True|False)(\\$[0-9])");
		Matcher m = p.matcher(jsA.toString());
		if (m.find()) {
			String lr = m.group(2).toString();
			if (lr.equals("False")) {
				return false;
			}else {
				return true;
			}
		}
		return false;
	}
	
	public static String findXFrameOptions(String documentResponse, JsonObject rawState) {
		
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/Server<:xframeOptions");
		String ansLine[] = jsA.toString().split(",");
		for (String line : ansLine) {
			Pattern p = Pattern.compile("(.*)->(.*)/(" + escapeRegexCharacters(documentResponse) + ")->(.*)(XFrameOptions\\$[0-9])");
			Matcher m = p.matcher(line);
			if (m.find()) {
				String xFrameOption = m.group(5).toString();
				jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/XFrameOptions<:option");
				String ansLine2[] = jsA.toString().split(",");
				for (String line2 : ansLine2) {
					p = Pattern.compile("(" + escapeRegexCharacters(xFrameOption) + ")->(.*)/(Deny|SameOrigin)(\\$[0-9])");
					m = p.matcher(line2);
					if (m.find()) {
						String option = m.group(3).toString();
						return option;
						/*if (option.equals("Deny")) {
							return "1";
						}else {
							return "2";
						}*/
					}
				}
				
				
				
			}
		}
		
		
		
		return "0";
	}
	
	public static String findFunctionUrl (String function, JsonObject rawState) {
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/" + function);
		Pattern p = Pattern.compile("(.*)/(ValidBlobUrl|BlobAbsoluteUrl|BlobOnlyDomainUrl|BlobNoPathUrl|AboutUrl|DataUrl|HttpsUrl|HttpUrl|StartupUrl|ErrorUrl)(\\$[0-9])");
		Matcher m = p.matcher(jsA.toString());
		if (m.find()) {
			
			return m.group(2).toString()+m.group(3).toString();
		}else {
			return "";
		}
	}
	
	public static String findFunctionProperty (String function, String pattern, JsonObject rawState) {
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/" + function);
		Pattern p = Pattern.compile(pattern);
		Matcher m = p.matcher(jsA.toString());
		if (m.find()) {
			
			return m.group(2).toString()+m.group(3).toString();
		}else {
			return "";
		}
	}
	
	
	public static BrowsingContext findBcInBcs(String name, Browser browser) {
		
		List<BrowsingContext> bcs = browser.bcs;
		
		for (BrowsingContext bc : bcs) {
			if (bc.name.equals(name)) {
				return bc;
			}
		}
		
		return null;
	}
	
	public static List<Media> findListOfMedia (JsonObject rawState, Browser browser) throws NoSuchFieldException, SecurityException, IllegalArgumentException, IllegalAccessException {
		
		List<Media> ms = new ArrayList<Media>();
		
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/Media");
		
		String ansLine[] = jsA.toString().split(",");
		
		for (String line : ansLine) {
			Pattern p = Pattern.compile("(.*)/(Media\\$[0-9])");
			Matcher m = p.matcher(line);
		    if(m.find()) {
		    	String mName = m.group(2).toString();
		    	Media media = new Media(mName);
		    	List<Domain> ds = findListOfDomainForMedia(mName, rawState, browser);
		    	media.permitted = ds;
		    	
		    	ms.add(media);
		    	
		    }
		}
		
		
		return ms;
	}
	
	public static Url findUrlByName (String name, Browser browser) {
		List<Url> urls = browser.urls;
		
		for (Url url : urls) {
			if (url.name.equals(name)) {
				return url;
			}
		}
		return null;
	}
	
	public static List<Url> findListOfUrls (JsonObject rawState) throws ClassNotFoundException, NoSuchMethodException, SecurityException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, NoSuchFieldException {
		List<Url> urls = new ArrayList<Url>();
		
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/Call<:urls");
		String ansLine[] = jsA.toString().split(",");
		for (String line : ansLine) {
			Pattern p = Pattern.compile("(.*)/(ValidBlobUrl|BlobAbsoluteUrl|BlobOnlyDomainUrl|BlobNoPathUrl|AboutUrl|DataUrl|HttpsUrl|HttpUrl|StartupUrl|ErrorUrl)(\\$[0-9])");
			Matcher m = p.matcher(line);
	    	if (m.find()) {

	    		Class<?> clazz = Class.forName("model.url."+m.group(2).toString());
	    		Constructor<?> constructor = clazz.getConstructor(String.class);
	    		Url instance = (Url) constructor.newInstance(m.group(2).toString()+m.group(3).toString());
	    		
	    		//TODO assign domain for http
	    		
	    		if (m.group(2).toString().matches("BlobAbsoluteUrl|BlobOnlyDomainUrl|HttpUrl|HttpsUrl")) {
	    			String pattern = "";
	    			boolean absUrl = false;
	    			if (m.group(2).toString().matches("HttpUrl|HttpsUrl")) {
	    				pattern = "scmexec/scmCallFunction/browser/url/AbsoluteUrl<:domain";
	    				absUrl = true;
	    			}else {
	    				pattern = "scmexec/scmCallFunction/browser/url/" + m.group(2).toString() + "<:domain";
	    			}
	    			JsonPrimitive jsA1 = rawState.getAsJsonPrimitive(pattern);
	    			String ansLine1[] = jsA1.toString().split(",");
	    			for (String line1 : ansLine1) {
	    				String[] leftRight = line1.split("->");
	    				Pattern p1 = Pattern.compile("scmexec/scmCallFunction/browser/url/" + escapeRegexCharacters(m.group(2).toString()+m.group(3).toString())   );
	    				Matcher m1 = p1.matcher(leftRight[0]);
	    				if (m1.find()) {
	    					p1 = Pattern.compile("(.*)/(Domain\\$[0-9])");
	    					m1 = p1.matcher(line1);
	    					if (m1.find()) {
	    						String dName = m1.group(2).toString();
	    						Domain d = new Domain(dName);
	    						clazz.getDeclaredField("domain").set(instance, d);
	    						if (absUrl) {
	    							pattern = "scmexec/scmCallFunction/browser/url/AbsoluteUrl<:path";
	    							jsA1 = rawState.getAsJsonPrimitive(pattern);
	    							String ansLine2[] = jsA1.toString().split(",");
	    							for (String line2 : ansLine2 ) {
	    								
	    								String[] leftRight2 = line2.split("->");
	    								p1 = Pattern.compile("scmexec/scmCallFunction/browser/url/" + escapeRegexCharacters(m.group(2).toString()+m.group(3).toString())   );
	    								m1 = p1.matcher(leftRight2[0]);
	    								if (m1.find()) {
	    									p1 = Pattern.compile("(.*)/(Path\\$[0-9])");
	    									m1 = p1.matcher(line2);
	    									if (m1.find()) {
	    										String path = m1.group(2).toString();
	    										clazz.getDeclaredField("path").set(instance, path);
	    									}
	    								}
	    								
	    							}
	    						}
	    						
	    					}
	    				}
	    			}
	    		}
	    		
	    		
	    		urls.add(instance);
	    	}
		}
		
		return urls;
	}
	
	public static List<Domain> findListOfDomainForMedia(String name, JsonObject rawState, Browser browser) throws SecurityException, IllegalArgumentException, IllegalAccessException {
		List<Domain> ds = new ArrayList<Domain>();
		JsonPrimitive jsA = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/Media<:permitted");
		
		String ansLine[] = jsA.toString().split(",");
		for (String line : ansLine) {
			String[] leftRight = line.split("->");
			Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/url/" + escapeRegexCharacters(name)   );
			Matcher m = p.matcher(leftRight[0]);
			
			if(m.find()) {
				p = Pattern.compile("(.*)/(Domain\\$[0-9])");
				m = p.matcher(line);
				if (m.find()) {
					String dName = m.group(2).toString();
					for (Url url : browser.urls) {
						
						try {
							Object o = url.getClass().getDeclaredField("domain").get(url);
							Domain d = (Domain) o;
							if (d.name.equals(dName)) {
								ds.add(d);
								break;
							}
							
							//System.out.println(o);
						}catch(NoSuchFieldException e) {
							
						}
						
						
					}
					
				}
			}
		}
		
		
		return ds;
	}
	


	
	public static List<BrowsingContext> assignNestedBcs(String name, JsonObject rawState, Browser browser){
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:nestedBcs");
		if (jsAs == null) {
			return null;
		}else {
			List<BrowsingContext> bcs = new ArrayList<BrowsingContext>();
			String[] allLine = jsAs.toString().split(",");
			for(String line : allLine) {
				String[] leftRight = line.split("->");
				Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
				Matcher m = p.matcher(leftRight[0]);
				if (m.find()) {
					p = Pattern.compile("(.*)/(BrowsingContext\\$[0-9])");
					m = p.matcher(leftRight[1]);
					if (m.find()) {
						String bcName = m.group(2).toString();
						BrowsingContext bc = assignBrowsingContext(bcName, rawState, browser);
						bcs.add(bc);
					}
				}
			}
			return bcs;
		}
		
		

	}
	
	public static BrowsingContext assignBrowsingContext(String name, JsonObject rawState, Browser browser){
		
		BrowsingContext bc = new BrowsingContext(name);
    	
    	
    	try {
    		bc.origin = assignBcOrigin(bc.name, rawState);
			bc.currentDoc = assignDocument(bc.name, rawState, browser);
			bc.nestedBcs = assignNestedBcs(bc.name, rawState, browser);
			
			bc.isSecureContext = assignSecureContext(bc.name, rawState);
			bc.isSandboxed = assignSandbox(name, rawState);
			bc.sandboxWaitingNavigate = assignSandboxWaitingNavigate(name, rawState);
			
			bc.win = assignWin(name, rawState);
			
			bc.opening = assignBcOpening(name, rawState, browser);
			
			if (bc.opening != null) {
				for (BrowsingContext brC : bc.opening) {
					BrowsingContext brC1 = findBcInBcs(brC.name, browser);
					if (brC1 == null) {
						browser.bcs.add(brC);
					}
				}
			}
			
			
			bc.accesses = assignBcAccesses(name, rawState, browser);
			
			bc.sessionHistory = assignBcHistory(name, rawState, browser);

			
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		return bc;
	}
	
	public static Media findMediaByName (String name, Browser browser) {
		
		List<Media> ms = browser.medias;
		
		for (Media m : ms) {
			if(m.name.equals(name)) {
				return m;
			}
		}
		
		
		return null;
	}
	
	public static List<Media> assignBcAccesses(String name, JsonObject rawState, Browser browser ){
		
		
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:accesses");
		
		if (jsAs == null) {
			return null;
		}else {
			List<Media> ms = new ArrayList<Media>();
			String[] allLine = jsAs.toString().split(",");
			
			for (String line : allLine) {
				String[] leftRight = line.split("->");
				Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
				Matcher m = p.matcher(leftRight[0]);
				if(m.find()) {
					p = Pattern.compile("(.*)/(Media\\$[0-9])");
					m = p.matcher(line);
					if (m.find()) {
						String mName = m.group(2).toString();
						Media media = findMediaByName(mName, browser);
						
						ms.add(media);
					}
					
				}
			}
			
			return ms;
		}
		
	}
	
	public static List<History> assignBcHistory (String name, JsonObject rawState, Browser browser) {
		
		
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:sessionHistory");
		if (jsAs == null) {
			return null;
		}else {
			List<History> hs = new ArrayList<History>();
			String[] allLine = jsAs.toString().split(",");
			
			for (String line : allLine) {
				
				String[] leftRight = line.split("->");
				Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
				Matcher m = p.matcher(leftRight[0]);
				if(m.find()) {
					p = Pattern.compile("(.*)/(History\\$[0-9])");
					m = p.matcher(line);
			    	if (m.find()) {
			    		String hName = m.group(2).toString();
			    		History h = new History(hName);
			    		h.url = assignBcHistoryUrl(hName, rawState, browser);
			    		hs.add(h);
			    		
			    	}
				}
				
			}
			
			
			return hs;
		}
		
	}
	
	public static Url assignBcHistoryUrl (String name, JsonObject rawState, Browser browser) {
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:sessionHistory");
		String[] allLine = jsAs.toString().split(",");
		
		for (String line : allLine) {
			String[] leftRight = line.split("->");
			Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/history/" + escapeRegexCharacters(name)   );
			Matcher m = p.matcher(leftRight[0]);
			
			if(m.find()) {
				p = Pattern.compile("(.*)/(ValidBlobUrl|BlobAbsoluteUrl|BlobOnlyDomainUrl|BlobNoPathUrl|AboutUrl|DataUrl|HttpsUrl|HttpUrl|StartupUrl|ErrorUrl)(\\$[0-9])");
				m = p.matcher(leftRight[1]);
		    	if (m.find()) {
		    		return findUrlByName(m.group(2).toString()+m.group(3).toString(), browser);
		    		
		    	}
			}
			
		}
		
		return null;
	}
	
	public static List<BrowsingContext> assignBcOpening(String name, JsonObject rawState, Browser browser){
		
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:opening");
		if (jsAs == null) {
			return null;
		}else {
			List<BrowsingContext> bcs = new ArrayList<BrowsingContext>();
			String[] allLine = jsAs.toString().split(",");
			
			for (String line : allLine) {
				String[] leftRight = line.split("->");
				Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
				Matcher m = p.matcher(leftRight[0]);
				if(m.find()) {
					p = Pattern.compile("(.*)/(BrowsingContext\\$[0-9])");
					m = p.matcher(line);
			    	if (m.find()) {
			    		String bcName = m.group(2).toString();
			    		BrowsingContext bc = findBcInBcs(bcName, browser);
			    		
			    		if (bc == null) {
			    			bc = assignBrowsingContext(bcName, rawState, browser);	
			    		}
			    		bcs.add(bc);
			    	}
				}
			}
			
			
			return bcs;
		}
		
	}
	
	public static Window assignWin(String name, JsonObject rawState) {
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:win");
		String[] allLine = jsAs.toString().split(",");
		
		for (String line : allLine) {
			String[] leftRight = line.split("->");
			Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
		    Matcher m = p.matcher(leftRight[0]);
		    if(m.find()) {
		    	p = Pattern.compile("(.*)/(TopLWindow|Iframe)(\\$[0-9])");
		    	m = p.matcher(line);
		    	if (m.find()) {
		    		String scStr = m.group(2).toString();
		    		if (scStr.equals("TopLWindow")) {
		    			return Window.TopLWindow;
		    		}else {
		    			return Window.Iframe;
		    		}
		    	}
		    }
		}
		
		return null;
	}
	
	public static Boolean assignSandboxWaitingNavigate(String name, JsonObject rawState) {
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:sandboxWaitingNavigate");
		
		if (jsAs == null) {
			return false;
		}else {
			return returnBooleanValue(name, jsAs);
		}
	}
	
	public static Boolean assignSandbox(String name, JsonObject rawState) {
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:isSandboxed");
		
		if (jsAs == null) {
			return false;
		}else {
			return returnBooleanValue(name, jsAs);
		}
	}
	
	public static Boolean assignSecureContext(String name, JsonObject rawState) {
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:isSecureContext");
		
		if (jsAs == null) {
			return false;
		}else {
			return returnBooleanValue(name, jsAs);
		}
		
		
		
	}
	
	public static Boolean returnBooleanValue(String name,  JsonPrimitive jsAs) {
		
		String[] allLine = jsAs.toString().split(",");
		
		for (String line : allLine) {
			String[] leftRight = line.split("->");
			Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
		    Matcher m = p.matcher(leftRight[0]);
		    if(m.find()) {
		    	p = Pattern.compile("(.*)/(True|False)(\\$[0-9])");
		    	m = p.matcher(line);
		    	if (m.find()) {
		    		String scStr = m.group(2).toString();
		    		if (scStr.equals("True")) {
		    			return true;
		    		}else {
		    			return false;
		    		}
		    	}
		    }
		}
		return false;
		
	}
	
	public static Origin assignBcOrigin(String name, JsonObject rawState) throws IllegalArgumentException, IllegalAccessException, NoSuchFieldException, SecurityException {
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:origin");
		
		String[] allLine = jsAs.toString().split(",");
		for (String line : allLine) {
			String[] leftRight = line.split("->");
			
			Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
		    Matcher m = p.matcher(leftRight[0]);
		    if(m.find()) {
		    	
		    	p = Pattern.compile("(.*)/(StartupOrigin|BlankOrigin|OpaqueOrigin|TupleOrigin)(\\$[0-9])");
		    	m = p.matcher(line);
		    	if(m.find()) {
		    		
		    		String originStr = m.group(2).toString();
		    		Origin origin;
		    		if (originStr.equals("StartupOrigin")) {
		    			
		    			origin = StartupOrigin.getInstance();
		    			
		    		}else if (originStr.equals("BlankOrigin")) {
		    			
		    			origin = BlankOrigin.getInstance();
		    			
		    		}else if (originStr.equals("OpaqueOrigin")) {
		    			
		    			origin = OpaqueOrigin.getInstance();
		    		}else {
		    			//TODO tuple origin not tested enough
		    			
		    			origin = new TupleOrigin(m.group(2).toString() + m.group(3).toString());
		    			jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/TupleOrigin<:scheme");
		    			String[] allLine2 = jsAs.toString().split(",");
		    			String browsingContextStr = m.group(2).toString() + escapeRegexCharacters(m.group(3).toString());
		    			for (String line2 : allLine2) {
		    				String[] leftRight2 = line2.split("->");
		    				
		    				p = Pattern.compile("scmexec/scmCallFunction/browser/url/" + browsingContextStr   );
		    				m = p.matcher(leftRight2[0]);
		    				if (m.find()) {
		    					p = Pattern.compile("(.*)/(Http|Https)(\\$[0-9])");
		    					m = p.matcher(leftRight2[1]);
		    					if (m.find()) {
		    						String schStr = m.group(2).toString();
			    					if (schStr.equals("Http")) {
			    						origin.getClass().getDeclaredField("scheme").set(origin, Scheme.Http);
			    					}else {
			    						origin.getClass().getDeclaredField("scheme").set(origin, Scheme.Https);
			    					}
			    					//return origin;
			    					
			    					jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/TupleOrigin<:domain");
			    					String[] allLine3 = jsAs.toString().split(",");
			    					for (String line3 : allLine3) {
			    						String[] leftRight3 = line3.split("->");
			    						p = Pattern.compile("scmexec/scmCallFunction/browser/url/" + browsingContextStr   );
			    						m = p.matcher(leftRight3[0]);
			    						if (m.find()) {
			    							p = Pattern.compile("(.*)/(Domain\\$[0-9])");
			    							m = p.matcher(leftRight3[1]);
			    							if (m.find()) {
			    								String domStr = m.group(2).toString();//NOTE this is not used, it is because the domain name example.com in LiveBcInfo.domain doesnt match if we assign something like Domain$2 here
			    								Domain dom = new Domain("example.com");
			    								origin.getClass().getDeclaredField("hostName").set(origin, dom );
			    								return origin;
			    							}
			    						}
			    					}
		    					}
		    					
		    				}
		    			}
		    		}
		    		
		    		return origin;
		    			
		    	}
		    }
		}
		return StartupOrigin.getInstance();
	}
	
	public static Document assignDocumentNested (String docStr, JsonObject rawState, Browser browser) {
		
		Document document = new Document(docStr);
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/Document<:src");
		
		Pattern p;
	    Matcher m;
		
		if (jsAs != null) {
			String[] allLine2 = jsAs.toString().split(",");
			for (String line2 : allLine2) {
				String[] leftRight2 = line2.split("->");
				p = Pattern.compile("scmexec/scmCallFunction/browser/url/" + escapeRegexCharacters(docStr)   );
			    m = p.matcher(leftRight2[0]);
			    if (m.find()) {
			    	
			    	p = Pattern.compile("(.*)/(ValidBlobUrl|BlobAbsoluteUrl|BlobOnlyDomainUrl|BlobNoPathUrl|AboutUrl|DataUrl|HttpsUrl|HttpUrl|StartupUrl|ErrorUrl)(\\$[0-9])");
			    	m = p.matcher(leftRight2[1]);
			    	if (m.find()) {
			    		//System.out.println(m.group(2).toString()+m.group(3).toString());
			    		
//			    		Class<?> clazz = Class.forName("model.url."+m.group(2).toString());
//			    		Constructor<?> constructor = clazz.getConstructor(String.class);
//			    		Object instance = constructor.newInstance(m.group(2).toString()+m.group(3).toString());
//			    		//System.out.println(instance);
//			    		document.src = (Url) instance;
			    		
			    		document.src = findUrlByName(m.group(2).toString()+m.group(3).toString(), browser);
			    		
			    		//also assign domain for Http/s urls
			    		
			    		
			    		JsonPrimitive jsAs2 = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/url/Document<:elements");
			    		if (jsAs2 != null) {
			    			
			    			String[] allLine3 = jsAs2.toString().split(",");
			    			for (String line3 : allLine3) {
			    				String[] leftRight3 = line3.split("->");
			    				
			    				p = Pattern.compile("scmexec/scmCallFunction/browser/url/" + escapeRegexCharacters(docStr)   );
			    				m = p.matcher(leftRight3[0]);
			    				if (m.find()) {
			    					p = Pattern.compile("(.*)/(Document\\$[0-9])");
			    					m = p.matcher(leftRight3[1]);
			    					if (m.find()) {
			    						//System.out.println(m.group(2).toString());
			    						Document docNested = assignDocumentNested(m.group(2).toString(), rawState, browser);
			    						document.elements.add(docNested);
			    					}
			    				}
			    				
			    				
			    			}
			    			
			    		}else {
			    			//document.elements = null;
			    		}
			    	}
			    }
			}
			
		}
		
		return document;
	}
	
	public static Document assignDocument(String name, JsonObject rawState, Browser browser) {
		
		JsonPrimitive jsAs = rawState.getAsJsonPrimitive("scmexec/scmCallFunction/browser/BrowsingContext<:currentDoc");
		
		if (jsAs != null) {
			
		
			String[] allLine = jsAs.toString().split(",");
			for (String line : allLine) {
				String[] leftRight = line.split("->");
				
				Pattern p = Pattern.compile("scmexec/scmCallFunction/browser/" + escapeRegexCharacters(name)   );
			    Matcher m = p.matcher(leftRight[0]);
			    
			    if (m.find()) {
			    	p = Pattern.compile("(.*)/(Document\\$[0-9])");
			    	m = p.matcher(line);
			    	if(m.find()) {
			    		String docStr = m.group(2).toString();
			    		
			    		Document document = assignDocumentNested(docStr, rawState, browser);
			    		
			    		
			    		return document;
			    	}
			    }
				
			}
		}
		return null;
		
		
	}
	
	
	
	public static String escapeRegexCharacters(String input) {
        String[] specialChars = { "\\", ".", "^", "$", "*", "+", "?", "|", "{", "}", "[", "]", "(", ")" };
        for (String ch : specialChars) {
            input = input.replace(ch, "\\" + ch);
        }
        return input;
    }

}
