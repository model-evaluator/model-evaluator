package exec;

import java.net.MalformedURLException;
import java.net.URL;

import org.openqa.selenium.Alert;
import org.openqa.selenium.By;
import org.openqa.selenium.JavascriptExecutor;
import org.openqa.selenium.UnexpectedAlertBehaviour;
import org.openqa.selenium.UnhandledAlertException;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.WebElement;
import org.openqa.selenium.chrome.ChromeDriver;
import org.openqa.selenium.interactions.Actions;
import org.openqa.selenium.logging.LogEntries;
import org.openqa.selenium.logging.LogEntry;
import org.openqa.selenium.logging.LogType;
import org.openqa.selenium.remote.CapabilityType;
import org.openqa.selenium.remote.DesiredCapabilities;
import org.openqa.selenium.remote.RemoteWebDriver;
import org.openqa.selenium.support.ui.ExpectedConditions;
import org.openqa.selenium.support.ui.WebDriverWait;


import java.util.Date;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.concurrent.TimeUnit;	

public class TestExecutor {
	
	public static final String AUTOMATE_USERNAME = "***";
	public static final String AUTOMATE_ACCESS_KEY = "***";
	public static final String URL = "https://" + AUTOMATE_USERNAME + ":" + AUTOMATE_ACCESS_KEY + "@hub-cloud.browserstack.com/wd/hub";
	
	public static void executeSample() throws MalformedURLException {
		DesiredCapabilities caps = new DesiredCapabilities();
	    caps.setCapability("os_version", "Mojave");
	    caps.setCapability("resolution", "1920x1080");
	    caps.setCapability("browser", "Safari");
	    caps.setCapability("browser_version", "12.1");
	    caps.setCapability("os", "OS X");
	    caps.setCapability("name", "BStack-[Java] Sample Test"); // test name
	    caps.setCapability("build", "BStack Build Number 1"); 
	    WebDriver driver = new RemoteWebDriver(new URL(URL), caps);
	    driver.get("https://www.google.com");
	    WebElement element = driver.findElement(By.name("q"));
	    element.sendKeys("BrowserStack");
	    element.submit();
	    // Setting the status of test as 'passed' or 'failed' based on the condition; if title of the web page contains 'BrowserStack'
	    WebDriverWait wait = new WebDriverWait(driver, 5);
	    try {
	    	wait.until(ExpectedConditions.titleContains("BrowserStack"));
	    	markTestStatus("passed","Yaay title contains 'BrowserStack'!",driver);
	    }
	    catch(Exception e) {
	    	markTestStatus("failed","Naay title does not contain 'BrowserStack'!",driver);
	    }
	    System.out.println(driver.getTitle());
	    driver.quit();
	}

	public static void alertOrigin() throws MalformedURLException {

			DesiredCapabilities caps = new DesiredCapabilities();
		    caps.setCapability("os_version", "Mojave");
		    caps.setCapability("resolution", "1920x1080");
		    caps.setCapability("browser", "Safari");
		    caps.setCapability("browser_version", "12.1");
		    caps.setCapability("os", "OS X");
		    caps.setCapability("name", "BStack-[Java] Sample Test"); // test name
		    caps.setCapability("build", "BStack Build Number 2"); 
		    caps.setCapability(CapabilityType.UNEXPECTED_ALERT_BEHAVIOUR, UnexpectedAlertBehaviour.IGNORE);
		    WebDriver driver = new RemoteWebDriver( new URL(URL), caps);
		try{

			
		    JavascriptExecutor js = (JavascriptExecutor)driver;
		    driver.get("https://www.google.de");

		    driver.manage().timeouts().setScriptTimeout(20, TimeUnit.SECONDS);

		    long start_time = System.currentTimeMillis();
		    js.executeAsyncScript("window.setTimeout(arguments[arguments.length - 1], 5000);");
			System.out.println("Passed time: " + (System.currentTimeMillis() - start_time));
			String text = (String) js.executeScript("return window.location.origin");
			System.out.println("Origin: " + text);
		    js.executeScript("alert('Welcome to Guru99');");
		    
		    

		}catch(UnhandledAlertException e){
			Alert alert = driver.switchTo().alert();
		    alert.accept();
		}
		markTestStatus("passed","",driver);
		    
		    driver.quit();
		
	}

	public static void returnOrigin() throws MalformedURLException, InterruptedException {
		WebDriver driver = new ChromeDriver();
		driver.get("http://iesiyok.de");
		Thread.sleep(5000);
		JavascriptExecutor js = (JavascriptExecutor)driver;
		String text = (String) js.executeScript("return window.location.origin");

		System.out.println("Origin: " + text);
		
		driver.manage().timeouts().implicitlyWait(50, TimeUnit.SECONDS);
		driver.quit();

	}

	public static void safariCameraAttack() throws MalformedURLException, InterruptedException {
		DesiredCapabilities caps = new DesiredCapabilities();
	    caps.setCapability("os_version", "Mojave");
	    caps.setCapability("resolution", "1920x1080");
	    caps.setCapability("browser", "Safari");
	    caps.setCapability("browser_version", "12.1");
	    caps.setCapability("os", "OS X");
	    caps.setCapability("name", "BStack-[Java] Sample Test"); // test name
		caps.setCapability("build", "BStack Build Number 3"); 
		caps.setCapability("browserstack.console", "info"); 
	    WebDriver driver = new RemoteWebDriver(new URL(URL), caps);
		driver.get("https://bugpoc.com/organizations/view");
		WebElement pb1= driver.findElement(By.id("bugpoc-id"));
		pb1.sendKeys("bp-HHAQuUYC");
		Thread.sleep(200);
		WebElement pb2= driver.findElement(By.id("bugpoc-password"));
		pb2.sendKeys("blahWrasse59");
		Thread.sleep(200);
		WebElement pb3= driver.findElement(By.id("view-poc-button"));
		pb3.click();
		Thread.sleep(4000);

		WebElement pb4= driver.findElement(By.className("newtypebutton"));
		pb4.click();
		Thread.sleep(2000);

		Set<String> handles = driver.getWindowHandles(); // get all window handles
		Iterator<String> iterator = handles.iterator();
		String sh = iterator.next();
		driver.switchTo().window(sh); 

		List<WebElement> pb5= driver.findElements(By.tagName("body"));
		pb5.get(0).click();

		Thread.sleep(1000);
		driver.close();
		markTestStatus("passed","",driver);
		driver.quit();
		
		
	    
	}
	
	public static void markTestStatus(String status, String reason, WebDriver driver) {
		JavascriptExecutor jse = (JavascriptExecutor)driver;
		jse.executeScript("browserstack_executor: {\"action\": \"setSessionStatus\", \"arguments\": {\"status\": \""+status+"\", \"reason\": \""+reason+"\"}}");
	}

}
