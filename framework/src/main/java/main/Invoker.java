package main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.openqa.selenium.By;
import org.openqa.selenium.Capabilities;
import org.openqa.selenium.JavascriptExecutor;
import org.openqa.selenium.Keys;
import org.openqa.selenium.MutableCapabilities;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.WebElement;
import org.openqa.selenium.chrome.ChromeDriver;
import org.openqa.selenium.devtools.DevTools;
import org.openqa.selenium.interactions.Actions;
import org.openqa.selenium.remote.DesiredCapabilities;
import org.openqa.selenium.safari.SafariDriver;
import org.openqa.selenium.safari.SafariOptions;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;
import org.openqa.selenium.remote.RemoteWebDriver;

import model.BrowsingContext;
import model.Document;
import model.ImplementationState;
import model.Window;
import model.url.BlankOrigin;
import model.url.Domain;
import model.url.OpaqueOrigin;
import model.url.Scheme;
import model.url.StartupOrigin;
import model.url.TupleOrigin;
import model.url.Url;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;

import java.util.UUID;
import java.util.stream.Collectors;

public class Invoker {
	
	public WebDriver driver;
	
	//public DevTools devTool;
	
	//public static final String USERNAME = "******";
    //public static final String AUTOMATE_KEY = "*********";
    //public static final String URL = "https://" + USERNAME + ":" + AUTOMATE_KEY + "@hub-cloud.browserstack.com/wd/hub";
	
	public Invoker() throws IOException {
		
		File file = new File("authentication.txt");
		FileReader fr = new FileReader(file);
		BufferedReader br = new BufferedReader(fr);
		
		String USERNAME;
		String AUTOMATE_KEY;
		String URL;

		USERNAME = br.readLine();
		AUTOMATE_KEY = br.readLine();
		fr.close();
		URL = "https://" + USERNAME + ":" + AUTOMATE_KEY + "@hub-cloud.browserstack.com/wd/hub";

		
		//driver = new SafariDriver();
		
		SafariOptions options = new SafariOptions();

        DesiredCapabilities capabilities = new DesiredCapabilities();
        
        DesiredCapabilities webkitCapabilities = new DesiredCapabilities();
        webkitCapabilities.setCapability("DisableICECandidateFiltering", true);
        webkitCapabilities.setCapability("DisableInsecureMediaCapture", true);

        // Set the nested capability on the primary capabilities object
        capabilities.setCapability("webkit:WebRTC", webkitCapabilities.asMap());
        capabilities.setCapability("browserstack.consoleLogs", "info");

		capabilities.setCapability("browserName", "Safari");
		HashMap<String, Object> browserstackOptions = new HashMap<String, Object>();
		browserstackOptions.put("os", "OS X");
		browserstackOptions.put("osVersion", "Mojave");
		browserstackOptions.put("browserVersion", "12.0");
		browserstackOptions.put("local", "false");
		browserstackOptions.put("seleniumVersion", "3.14.0");
		
		capabilities.setCapability("bstack:options", browserstackOptions);

        // Merge primary capabilities with Safari options
        options.merge(capabilities);


		try {
			driver = new RemoteWebDriver(new URL(URL), capabilities);
		} catch (MalformedURLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		

	}
	
	public ImplementationState invokeNewTab(boolean firstTabControl) {
		
		String handle = "";
		
		if (!firstTabControl) {

			JavascriptExecutor jse = (JavascriptExecutor) driver;
			jse.executeScript("window.open()");	
			try {
				Thread.sleep(2000);
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		handle = tabs.get(tabs.size()-1);
		driver.switchTo().window(handle);
		
		ImplementationState liveBcInfo = takeAllBcs(firstTabControl, tabs);
		liveBcInfo.currentHandle = handle;
		//BrowsingContext bc = takeBCLiveInfo(firstTabControl, driver.getWindowHandle(), nameHandleMap, false, true);
		
		return liveBcInfo;
		
	}
	
	public ImplementationState invokeNavigate(String url, String handle, String nestedHandle, boolean locationReplace) {
		driver.switchTo().window(handle);
		
		if (!handle.equals(nestedHandle)) {
			driver.switchTo().frame(nestedHandle);
		}
		
		if (locationReplace) {
			String script = "location.replace('"+url+"');"; 
			((JavascriptExecutor) driver).executeScript(script);
		}else {
			String script = 
					  "var a = document.createElement('a');" +
					  "a.href = 'https://google.com';" +
					  "a.style.display = 'none';" + // Makes the link invisible
					  "document.body.appendChild(a);" +
					  "a.click();";

					((JavascriptExecutor) driver).executeScript(script);
		}
		
		
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		liveBcInfo.currentHandle = handle;
		liveBcInfo.errorMessage = "";
		return liveBcInfo;
	} 
	
	public ImplementationState invokeCreateBlob(String handle) {
		driver.switchTo().window(handle);
		String script = "var blob = new Blob(['Hello, world!'], {type: 'text/plain'});" +
                "return window.URL.createObjectURL(blob);"; 
		String blobUrl = (String) ((JavascriptExecutor) driver).executeScript(script);
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		liveBcInfo.currentHandle = handle;
		liveBcInfo.correspondingUrl = blobUrl;
		liveBcInfo.errorMessage = "";
		return liveBcInfo;
		
	}
	
	public ImplementationState invokeHistoryPushState(String url, String handle, String nestedHandle) {
		driver.switchTo().window(handle);
		if (!handle.equals(nestedHandle)) {
			driver.switchTo().frame(nestedHandle);
		}
		String script = "history.pushState(\"\",\"\",\""+ url+"\")"; 
		String error = "";
		try {
			((JavascriptExecutor) driver).executeScript(script);
		}catch(Exception e) {
			error = e.getLocalizedMessage();
		}
		
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		liveBcInfo.currentHandle = handle;
		liveBcInfo.errorMessage = error;
		return liveBcInfo;
		
	}
	
	public ImplementationState invokeCreateIframe (String url, String handle) {
		driver.switchTo().window(handle);
		String error = "";
		String id = "iframe-" + UUID.randomUUID().toString();
		String script = "let iframe = document.createElement('iframe'); iframe.src = '" + url + "'; iframe.id='" + id + "'; document.body.appendChild(iframe);";
		JavascriptExecutor js = (JavascriptExecutor) driver;
		try {
			js.executeScript(script);
		}catch (Exception e) {
			error = e.getLocalizedMessage();
		}
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		liveBcInfo.currentHandle = handle;
		liveBcInfo.errorMessage = error;
		liveBcInfo.newBc = id;
		return liveBcInfo;
        

	}
	
	public ImplementationState invokeDocumentWrite2Child(String handle, String targetId) {
		driver.switchTo().window(handle);
		
		String error = "";
		JavascriptExecutor js = (JavascriptExecutor) driver;
		String script = "document.getElementById('" + targetId + "').contentDocument.write('Document write applied');";
		try {
			js.executeScript(script);
		}catch (Exception e) {
			error = e.getLocalizedMessage();
		}
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		liveBcInfo.currentHandle = handle;
		liveBcInfo.errorMessage = error;
		return liveBcInfo;
	}
	
	public ImplementationState invokePopup(String url, String handle, String nestedHandle) {
		driver.switchTo().window(handle);
		
		if (!handle.equals(nestedHandle)) {
			driver.switchTo().frame(nestedHandle);
		}
		String error = "";
		
		Set<String> originalHandles = driver.getWindowHandles();
		
		
		JavascriptExecutor js = (JavascriptExecutor) driver;
		
		String script = "window.newWindow = window.open('" + url + "', 'newWindow');";
		
		js.executeScript(script);
		
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		
		
		Set<String> currentHandles = driver.getWindowHandles();
		Set<String> newHandles = currentHandles.stream()
                .filter(handle2 -> !originalHandles.contains(handle2))
                .collect(Collectors.toSet());

		String newTabHandle = newHandles.iterator().next();
		
		driver.switchTo().window(newTabHandle);

		
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		liveBcInfo.currentHandle = newTabHandle;
		liveBcInfo.errorMessage = error;
		
		return liveBcInfo;
	} 
	
	public ImplementationState invokeDocumentWrite2Popup(String handle, String nestedHandle, String windowReference) {
		driver.switchTo().window(handle);
		
		if (!handle.equals(nestedHandle)) {
			driver.switchTo().frame(nestedHandle);
		}
		String error = "";

		
		String script = "newWindow.document.write('Hello there');";
		


		JavascriptExecutor js = (JavascriptExecutor) driver;
		try {
			js.executeScript(script);
		}catch (Exception e) {
			error = e.getLocalizedMessage();
		}
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		driver.switchTo().window(windowReference);
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		liveBcInfo.errorMessage = error;
		liveBcInfo.currentHandle = windowReference;
		return liveBcInfo;
	}
	
	public ImplementationState invokeAccess2Media(String handle) {
		driver.switchTo().window(handle);
		
		JavascriptExecutor js = (JavascriptExecutor) driver;

		//  Insert the script into the document
		String script = 
				"var scriptElement = document.createElement('script');\n" +
				"scriptElement.textContent = `" +
			    "function hackCamera(){ " +               
			    "    document.body.innerHTML='<video style=\"margin:0; border: 0; width: 100%; height: 100%\" autoplay playsinline></video>';" + 
			    "    const constraints = window.constraints = {" +
			    "        audio: true," +
			    "        video: true" +
			    "    };" +
			    "    async function init() {" +
			    "        try {" +
			    "            const stream = await navigator.mediaDevices.getUserMedia(constraints);" +
			    "            handleSuccess(stream);" +
			    "        } catch (e) {" +
			    "            console.log(e);" +
			    "        }" +
			    "    }" +
			    "    function handleSuccess(stream) {" +
			    "        const video = document.querySelector('video');" +
			    "        const videoTracks = stream.getVideoTracks();" +
			    "        window.stream = stream;" +
			    "        video.srcObject = stream;" +
			    "    }" +
			    "    init();" +
			    "}`;\n" + 
			    "document.body.appendChild(scriptElement);\n" + 
			    "setTimeout(function() {console.log('Wait here');}, 3000);\n" +
			    "hackCamera();";
		
		
		
		String error = "";
		try {
			js.executeScript(script);
		}catch (Exception e) {
			error = e.getLocalizedMessage();
		}
		
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		String script3 = "let callback = arguments[arguments.length - 1];" + 
                "navigator.mediaDevices.enumerateDevices().then(function(devices) { callback(devices); }).catch(function(err) { callback(err); });";

		Object result = ((JavascriptExecutor) driver).executeAsyncScript(script3);
		
		boolean cameraInUse = false;

		if (result instanceof List<?>) {
		    List<Map<String, Object>> devices = (List<Map<String, Object>>) result;
		    cameraInUse = devices.stream().anyMatch(device -> "videoinput".equals(device.get("kind")) /*&& "live".equals(device.get("readyState"))*/);
		    System.out.println("cameraInUSE:: " + cameraInUse );
		} else {
		    // Handle error
			cameraInUse = false;
		    System.out.println("Error fetching devices: " + result);
		}


		
		ArrayList<String> tabs = new ArrayList<String>(driver.getWindowHandles());
		ImplementationState liveBcInfo = takeAllBcs(false, tabs);
		
		liveBcInfo.errorMessage = error;
		liveBcInfo.currentHandle = handle;
		liveBcInfo.cameraInUse = cameraInUse;
		return liveBcInfo;
	}
	
	public ImplementationState takeAllBcs(boolean firstTabControl, ArrayList<String> handles ) {
		List<BrowsingContext> bcs = new ArrayList<BrowsingContext>();
		for (String handle : handles) {
			BrowsingContext bc = takeBCLiveInfo(firstTabControl, handle, false, true);
			bcs.add(bc);
		}
		ImplementationState liveBcInfo = new ImplementationState();
		liveBcInfo.bcs = bcs;
		
		return liveBcInfo;
	}
	

	
	public BrowsingContext takeBCLiveInfo(boolean firstTabControl, String handle, boolean isSandboxed, boolean topLevel) {
		
		BrowsingContext liveBc = new BrowsingContext(handle);
		
		if(topLevel) {
			
			driver.switchTo().window(handle);
			
		}
		
		
		JavascriptExecutor jse = (JavascriptExecutor) driver;
		boolean isSecure = (boolean) jse.executeScript("return window.isSecureContext;");
		
		String origin = (String) jse.executeScript("var x = origin; return x;");
		String urlStr = (String) jse.executeScript("return window.location.href;");
		
		
		System.out.println(handle + " Href:: " + urlStr + " Origin:: " + origin + " SC:: " + isSecure);

		
		if (firstTabControl) {
			liveBc.origin = StartupOrigin.getInstance();
	
			liveBc.currentDoc = null;
			liveBc.accesses = null;
	
		}else {
			liveBc.accesses = null;//TODO
			
			
			if (origin.equals("null")) {
				liveBc.origin = OpaqueOrigin.getInstance();
			}else if(origin.equals("://")) {
				liveBc.origin = BlankOrigin.getInstance();
			}else {
				
				String id = "tuple-" + handle;
				TupleOrigin to = new TupleOrigin(id);
				String ansLine[] = origin.toString().split("://");
				if(ansLine[0].equals("https")) {
					to.scheme = Scheme.Https;
				}else {
					to.scheme = Scheme.Http;
				}
				Domain d = new Domain(ansLine[1]);
				to.hostName = d;
				liveBc.origin = to;
				
			}
			
			
			
			Document doc = new Document();
			
			Url url = new Url(urlStr);
			url.scheme = findSchemeInUrlStr(urlStr);
			
			doc.name = handle;
			
			doc.src = url;
			doc.elements = new ArrayList<Document>();
			
			List<BrowsingContext> _nestedBcs = new ArrayList<BrowsingContext>();
			
			
			List<WebElement> iframes = driver.findElements(By.tagName("iframe"));
			for (WebElement iframe : iframes) {
				Document doc1 = new Document();
	            String sandbox = iframe.getAttribute("sandbox");
	            String src = iframe.getAttribute("src");
	            String id = iframe.getAttribute("id");
	            Url u = new Url(src);
	            u.scheme = findSchemeInUrlStr(src);
	            doc.elements.add(doc1);
	            doc1.name = id + "_doc";
	            
	            driver.switchTo().frame(id);
	            BrowsingContext nestedLiveBc;
	            if (sandbox != null && sandbox.equals("true")) {
	            	
	            	nestedLiveBc = takeBCLiveInfo(false, id, true, false);
	            	
	            }else {
	            	
	            	nestedLiveBc = takeBCLiveInfo(false, id, true, false);
	            }
	            
	            _nestedBcs.add(nestedLiveBc);
	            
	        }
			
			if (_nestedBcs.size() > 0) {
				liveBc.nestedBcs = _nestedBcs;
			}else {
				liveBc.nestedBcs = null;
			}
			liveBc.currentDoc = doc;
			
		}
		liveBc.opening = null;
		liveBc.sandboxWaitingNavigate = false;
		liveBc.sessionHistory = null;
		
		
		liveBc.isSecureContext = isSecure;
		liveBc.isSandboxed = isSandboxed;
		if (topLevel) {
			liveBc.win = Window.TopLWindow;
		}else {
			liveBc.win = Window.Iframe;
		}
		
		
		return liveBc;
	}
	
	public Scheme findSchemeInUrlStr(String urlStr) {
		String ansLine[] = urlStr.toString().split("://");
		if (ansLine.length > 1) {
			if(ansLine[0].equals("https")) {
				return Scheme.Https;
			}else {
				return Scheme.Http;
			}
		}else {
			ansLine = urlStr.toString().split(":");
			if(ansLine[0].equals("Data")) {
				return Scheme.Data;
			}else if(ansLine[0].equals("Blob")) {
				return Scheme.Blob;
			}else if(ansLine[0].equals("About")) {
				return Scheme.About;
			}
		}
		return null;
	}
	
	public void quit() {
		this.driver.quit();
	}

}
