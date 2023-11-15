package main;

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.javers.core.Javers;
import org.javers.core.JaversBuilder;
import org.javers.core.MappingStyle;
import org.javers.core.diff.Diff;
import org.javers.core.diff.ListCompareAlgorithm;
import org.javers.core.diff.changetype.ValueChange;
import org.openqa.selenium.By;
import org.openqa.selenium.WebElement;

import model.Browser;
import model.BrowsingContext;
import model.ModelDiffState;
import model.ImplementationState;
import model.OriginChange;
import model.function.Access2Media;
import model.function.CreateBlob;
import model.function.CreateIframe;
import model.function.DocumentWrite;
import model.function.HistoryPushState;
import model.function.LocationReplace;
import model.function.Navigate;
import model.function.Popup;
import model.url.HttpUrl;
import model.url.HttpsUrl;
import model.url.Origin;
import model.url.StartupOrigin;
import model.url.Url;

public class Interpreter {
	
	public List<Browser> rawStates;
	
	public List<ModelDiffState> diffList;
	
	public HashMap<String, String> nameHandleMap;
	
	public Invoker invoker;
	
	public Interpreter(List<Browser> rawStates, List<ModelDiffState> diffList  ) throws IOException {
		this.rawStates = rawStates;
		this.diffList = diffList;
		this.invoker = new Invoker();
		this.nameHandleMap = new HashMap<String, String>();
	}
	
	public String interpret() throws NoSuchMethodException, SecurityException, ClassNotFoundException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		
		
		ImplementationState prevLiveBcInfo = invoker.invokeNewTab(true);
		
		nameHandleMap.put(diffList.get(0).bc, prevLiveBcInfo.currentHandle);
		ImplementationState liveBcInfo = null;
		List<Url> listOfUrls = rawStates.get(0).urls;
		
		String result = "";
		
		for (int i = 0; i < diffList.size(); i++) {
			Browser rawState = rawStates.get(i);
			ModelDiffState diffState = diffList.get(i);
			
			String rootBc = diffState.rootBc;
			String bc = diffState.bc;
			String party = diffState.party;
			String event = diffState.event;
			
			System.out.println("STATE:: " + i + " EVENT:: " + event);
			
			if (!party.equals(bc)) {
				invoker.quit();
				System.out.println("STATE :: " + i + " applying party (" + party + ") and bc (" + bc + ") are different. This behaviour has not been developed yet." );
				System.exit(0);
			}
			
			
					
					if (event.equals("NewTab")) {
						
						liveBcInfo = invoker.invokeNewTab(false);
						nameHandleMap.put(bc, liveBcInfo.currentHandle);
						
					}else if (event.equals("Navigate") | event.equals("LocationReplace")) {
						
						String urlStr, xFrameOption;
						
						if (event.equals("Navigate")) {
							Navigate nav = (Navigate) rawState.function.event;
							urlStr = nav.url;
							xFrameOption = nav.xFrameOption;
						}else {
							LocationReplace lr = (LocationReplace) rawState.function.event;
							urlStr = lr.url;
							xFrameOption = lr.xFrameOption;
						}
						
						
						
						String handle = nameHandleMap.get(rootBc);
						String handle2 = handle;
						if (!rootBc.equals(bc)) {
							handle2 = nameHandleMap.get(bc);
						}
						
						for(Url url : listOfUrls) {
							if (url.name.equals(urlStr)) {
								if ((xFrameOption.equals("Deny") | (xFrameOption.equals("SameOrigin") && xFrameOptionsSameOriginCheckFails(rawState.bcs, bc, url)) ) && ((url instanceof HttpUrl) | (url instanceof HttpsUrl) )) {
									
									
									String xFrameUrl = HttpsUrl.xFrameCorresponding;
									
									liveBcInfo = invoker.invokeNavigate(xFrameUrl, handle, handle2, event.equals("LocationReplace"));
								}else {
									liveBcInfo = invoker.invokeNavigate(url.corresponding, handle, handle2, event.equals("LocationReplace"));
								}
								
							}
						}
						
					}else if (event.equals("CreateBlob")) {
						CreateBlob cb = (CreateBlob) rawState.function.event;
						String urlStr = cb.url;
						String handle = nameHandleMap.get(party);
						liveBcInfo = invoker.invokeCreateBlob( handle);
						for(int j = 0; j < listOfUrls.size(); j++) {
							Url url = listOfUrls.get(j);
							if (url.name.equals(urlStr)) {
								url.corresponding = liveBcInfo.correspondingUrl;
								listOfUrls.set(j, url);
							}
							
						}
						
					}else if (event.equals("HistoryPushState")) {
						HistoryPushState hps = (HistoryPushState) rawState.function.event;
						String targetUrl = hps.tarUrl;
						
						String handle = nameHandleMap.get(rootBc);
						String handle2 = handle;
						if (!rootBc.equals(bc)) {
							handle2 = nameHandleMap.get(bc);
						}
						for (Url url : listOfUrls) {
							if(url.name.equals(targetUrl)) {
								liveBcInfo = invoker.invokeHistoryPushState(url.corresponding, handle, handle2);
							}
						}
						
					}else if (event.equals("CreateIframe")) {
						CreateIframe ci = (CreateIframe) rawState.function.event;
						String urlStr = ci.url;
						String newBc = ci.newBc;
						String handle = nameHandleMap.get(party);
						for (Url url : listOfUrls) {
							if (url.name.equals(urlStr)) {
								liveBcInfo = invoker.invokeCreateIframe(url.corresponding, handle);
								nameHandleMap.put(newBc, liveBcInfo.newBc);
							}
						}
					}else if (event.equals("DocumentWrite")) {
						DocumentWrite dw = (DocumentWrite) rawState.function.event;
						String targetBc = dw.targetBc;
						String relation = findRelationBetweenTargetAndParty(targetBc, party, rawState);
						
						String handle = nameHandleMap.get(rootBc);
						String handle2 = handle;
						if (!rootBc.equals(bc)) {
							handle2 = nameHandleMap.get(bc);
						}
						String targetId = nameHandleMap.get(targetBc);
						
						if (relation == "-1") {
							System.out.println("Relationship between applying party " + party + " and target " + targetBc + " cannot be found in the abstract state");
						}else {
							if (relation == "0") {
								liveBcInfo = invoker.invokeDocumentWrite2Child(handle, targetId );
								
							}else {
								
								liveBcInfo = invoker.invokeDocumentWrite2Popup(handle, handle2, targetId);
							}
						}
					}else if (event.equals("Popup")) {
						Popup popup = (Popup) rawState.function.event;
						String urlStr = popup.url;
						String newBc = popup.newBc;
						String handle = nameHandleMap.get(rootBc);
						String handle2 = handle;
						if (!rootBc.equals(bc)) {
							handle2 = nameHandleMap.get(bc);
						}
						for (Url url : listOfUrls) {
							if (url.name.equals(urlStr)) {
								liveBcInfo = invoker.invokePopup(url.corresponding, handle, handle2);
								nameHandleMap.put(newBc, liveBcInfo.currentHandle);
								
							}
						}
					}else if (event.equals("Access2Media")) {
						
						String handle = nameHandleMap.get(party);
						liveBcInfo = invoker.invokeAccess2Media(handle);
					}
					
				
			
			String res = checkStatus(prevLiveBcInfo, liveBcInfo, diffState, nameHandleMap);
			
			if (!res.equals("")) {
				result += "STATE:: " + i + " :: " + res;
			}
			
			if(liveBcInfo.cameraInUse) {
				result += "STATE:: " + i + " :: " + " camera has been accessed by " + bc + " whose " + cameraInUseResult(liveBcInfo, nameHandleMap.get(bc)) ;
			}
			
			
			System.out.println("RESULT:: " + res);
			System.out.println("ERROR:: " + liveBcInfo.errorMessage);
			prevLiveBcInfo = liveBcInfo;
			int a = 0;
			
			
		}
		
		return result;
		
	}
	
	public boolean xFrameOptionsSameOriginCheckFails (List<BrowsingContext> bcs, String bcname, Url url) {
		
		for (BrowsingContext bc : bcs) {
			if (bc.name.equals(bcname)) {
				if (!bc.origin.originStr.equals(url.correspondingOrigin)) {
					return true;
				}
			}else {
				boolean x = xFrameOptionsSameOriginCheckFails(bc.nestedBcs, bcname, url);
				if (x) {
					return true;
				}
			}
		}
		
		return false;
	}
	
	
	public String cameraInUseResult (ImplementationState liveBcInfo, String bc) {
		
		for (BrowsingContext nbc : liveBcInfo.bcs) {
			if (nbc.name.equals(bc)) {
				return "URL:: " + nbc.currentDoc.src.name.toString() + ", Origin:: " + nbc.origin.toString() + " and Secure Context:: " + nbc.isSecureContext; 
			}
		}
		
		
		return null;
	}
	
	
	public String findRelationBetweenTargetAndParty (String targetBc, String party, Browser rawState) {
		String result = "";
		
		
		result = findRelationBetweenTargetAndPartyRoot(targetBc, party, rawState.bcs );
		if (result.equals("-1")) {
			for (BrowsingContext bc : rawState.bcs) {
				if (bc.nestedBcs != null && bc.nestedBcs.size() > 0) {
					result = findRelationBetweenTargetAndPartyRoot(targetBc, party, bc.nestedBcs );
					if (!result.equals("-1")) {
						return result;
					}
				}
			}
		}else {
			return result;
		}
		
		return "-1";
	}
	
	public String findRelationBetweenTargetAndPartyRoot (String targetBc, String party, List<BrowsingContext> bcs) {
		String result = "";
		
		for (BrowsingContext bc : bcs) {
			if (bc.name.equals(party)) {
				result = findRelationBetweenTargetAndPartyNested(bc.nestedBcs, targetBc);
				if (result == "0") {
					return "0";
				}else {
					result = findRelationBetweenTargetAndPartyOpening(bc.opening, targetBc);
					return result;
				}
			}
		}
		return "-1";
	}
	
	public String findRelationBetweenTargetAndPartyNested (List<BrowsingContext> childBcs, String targetBc) {
		
		for (BrowsingContext childBc : childBcs) {
			if (childBc.name.equals(targetBc)) {
				return "0";
			}
		}
		
		return "-1";
	}
	
	public String findRelationBetweenTargetAndPartyOpening (List<BrowsingContext> openingBcs, String targetBc) {
		
		for (BrowsingContext openingBc : openingBcs) {
			if (openingBc.name.equals(targetBc)) {
				return "1";
			}
		}
		
		return "-1";
	}
	
	public String checkStatus (ImplementationState prevLiveBcInfo, ImplementationState liveBcInfo, ModelDiffState diffState, HashMap<String, String> nameHandleMap ) {
		
		Javers javers = JaversBuilder.javers()
				.withListCompareAlgorithm(ListCompareAlgorithm.LEVENSHTEIN_DISTANCE)
				.withMappingStyle(MappingStyle.FIELD).build();

		Diff diff = javers.compare(prevLiveBcInfo, liveBcInfo);
		
		ModelDiffState diffState2 = new ModelDiffState();
		diff.getChangesByType(ValueChange.class).forEach(ch -> {
			
			if (ch.getAffectedGlobalId().getTypeName().equals("model.BrowsingContext")) {
				
					if (ch.getPropertyName().equals("isSecureContext")) {
						diffState2.valueChanges.add(ch);
					}
			}
				
			
		});
		for (BrowsingContext bc1 : prevLiveBcInfo.bcs) {
			for (BrowsingContext bc2 : liveBcInfo.bcs) {
				if (bc1.name.equals(bc2.name)) {
					if(!bc1.origin.equals(bc2.origin)) {
						OriginChange oc = new OriginChange();
						oc.bc = bc1;
						oc.initialOrigin = bc1.origin;
						oc.changeOrigin = bc2.origin;
						diffState2.originChanges.add(oc);
					}
				}
			}
		}
		
		String scRes = checkSecureContexts(diffState, diffState2, nameHandleMap);
		String originRes = checkOrigins(diffState, diffState2, nameHandleMap);
		
		return scRes + originRes;
		
	}
	
	public String checkOrigins (ModelDiffState diffState, ModelDiffState diff, HashMap<String, String> nameHandleMap) {
		String result = "";
		
		for (String name : nameHandleMap.keySet()) {
			result += checkOrigin (diffState, diff, name);
		}
		return result;
		
	}
	
	public String checkOrigin (ModelDiffState diffState, ModelDiffState diff, String name) {
		String result = "";

		boolean vcOriginChange = false;
		Origin vcOriginLeft = StartupOrigin.getInstance();
		Origin vcOriginRight = StartupOrigin.getInstance();
		
		for (OriginChange vc : diffState.originChanges) {
			BrowsingContext vcBc = vc.bc;
			if (vcBc.name.equals(name)) {
				vcOriginChange = true;
				vcOriginLeft = vc.initialOrigin;
				vcOriginRight = vc.changeOrigin;
			}
		}
		
		boolean chOriginChange = false;
		Origin chOriginLeft = StartupOrigin.getInstance();
		Origin chOriginRight = StartupOrigin.getInstance();
		
		for (OriginChange ch : diff.originChanges) {
			BrowsingContext chBc = ch.bc;
			if (chBc.name.equals(nameHandleMap.get(name))) {
				chOriginChange = true;
				chOriginLeft = ch.initialOrigin;
				chOriginRight = ch.changeOrigin;
			}
		}
		
		if (vcOriginChange == false && chOriginChange == false ) {
			
		}else {
			if (vcOriginChange == true && chOriginChange == true) {
				if (vcOriginLeft.equals(chOriginLeft) && vcOriginRight.equals(chOriginRight) ) {
					
				}else {
					result += "BC:: " + name + ", origin value changed from " + vcOriginLeft + " to " + vcOriginRight + " in abstract state, whereas in concrete state from " + chOriginLeft + " to " + chOriginRight + ".\n";
				}
			}else {
				if (vcOriginChange == false) {
					result += "BC:: " + name + ", origin value didnt change in abstract state, whereas in concrete state from " + chOriginLeft + " to " + chOriginRight + ".\n";
				}
				if (chOriginChange == false) {
					result += "BC:: " + name + ", origin value changed from " + vcOriginLeft + " to " + vcOriginRight + " in abstract state, whereas in concrete state didnt change.\n";
				}
				
			}
		}
			
		
		return result;
	}
	
	
	public String checkSecureContexts (ModelDiffState diffState, ModelDiffState diff, HashMap<String, String> nameHandleMap) {
		String result = "";
		
		for (String name : nameHandleMap.keySet()) {
			result += checkSecureContext(diffState, diff, name);
		}
		return result;
		
	}
	public String checkSecureContext(ModelDiffState diffState, ModelDiffState diff, String name) {
		
		String result = "";
		
		boolean vcSCChange = false;
		String vcSCLeft = "";
		String vcSCRight = "";
		
		for(ValueChange vc : diffState.valueChanges) {
			if (vc.getAffectedGlobalId().getTypeName().equals("model.BrowsingContext")) {
				BrowsingContext vcBc = (BrowsingContext) vc.getAffectedObject().get();
				
				if (vcBc.name.equals(name)) {
					if (vc.getPropertyName().equals("isSecureContext")) {
						vcSCChange = true;
						if (vc.getLeft() != null) {
							vcSCLeft = (String) vc.getLeft().toString();
						}else {
							vcSCLeft = "";
						}
						
						vcSCRight = (String) vc.getRight().toString();
					}
				}
				
				
				
			}
		}
		
		boolean chSCChange = false;
		String chSCLeft = "";
		String chSCRight = "";
		

		
		for(ValueChange ch : diff.valueChanges) {
			if (ch.getAffectedGlobalId().getTypeName().equals("model.BrowsingContext")) {
				BrowsingContext chBc = (BrowsingContext) ch.getAffectedObject().get();
				
				if (chBc.name.equals(nameHandleMap.get(name))) {
					if (ch.getPropertyName().equals("isSecureContext")) {
						chSCChange = true;
						if (ch.getLeft() != null) {
							chSCLeft = (String) ch.getLeft().toString();
						}else {
							chSCLeft = "";
						}
						
						chSCRight = (String) ch.getRight().toString();
					}
				}

			}
		}
		
		if (vcSCChange == false && chSCChange == false ) {
			
		}else {
			if (vcSCChange == true && chSCChange == true) {
				if (vcSCLeft.equals(chSCLeft) && vcSCRight.equals(chSCRight) ) {
					
				}else {
					result += "BC:: " + name + ", isSecureContext value changed from " + vcSCLeft + " to " + vcSCRight + " in abstract state, whereas in concrete state from " + chSCLeft + " to " + chSCRight + ".\n";
				}
			}else {
				if (vcSCChange == false) {
					result += "BC:: " + name + ", isSecureContext value didnt change in abstract state, whereas in concrete state from " + chSCLeft + " to " + chSCRight + ".\n";
				}
				if (chSCChange == false) {
					result += "BC:: " + name + ", isSecureContext value changed from " + vcSCLeft + " to " + vcSCRight + " in abstract state, whereas in concrete state didnt change.\n";
				}
				
			}
		}
		
			
			
		
		
		return result;
	}

}
