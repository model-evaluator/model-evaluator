package util;
import java.text.SimpleDateFormat;
import java.util.Date;

import model.*; 

public class Invoker {

	public Invoker (){

	}

	public static String targetDomain = "skype.com";

	public static SimpleDateFormat simpleDateFormat = new SimpleDateFormat("hhmmss");


	public static String properDataSchemeURL(String data){

		return "\"data:text/html," + data + "\"";

	}

	public static String windowOpen(String data){

		return "window.open(" + data + ", '_self');\n";

	}
	

	public static Window TCreateIframeWoSandbox(Window w){

		String dateAsString = simpleDateFormat.format(new Date());

		String str = "var iframe_" + dateAsString + " = document.createElement(\"iframe\");\n";
		str += "iframe_" + dateAsString + ".setAttribute('src', 'about:blank');\n";
		str += "iframe_" + dateAsString + ".setAttribute('id', 'iframe_" + dateAsString + "');\n";
		str += "document.getElementsByTagName('body')[0].append(iframe_" + dateAsString + ");\n";

		w.resultingStr = str;
		w.frame = "iframe_" + dateAsString;
		return w;
	}

	public static Window TPopup(Window w){
		String str = w.url;
		w.resultingStr = str;
		return w;
	}

	public static Window TNewBlob(Window w){
		
		//String str = "blob = new Blob(['<h1>hello, world!</h1>'], {type: 'text/html'});\n";
		String str = "let blobURL = URL.createObjectURL(new Blob(['<h1>hello, world!</h1>'], {type: 'text/html'}));\n";
		w.content = "blobURL";
		w.resultingStr = str;
		return w;
	}

	public static Window TLocationReplace(Window w){
		String str = "location.replace(" + w.content + ");\n";
		w.resultingStr = str;
		return w;
	}

	public static Window THistoryPushState_1(Window w){
		String str = "history.pushstate('','', 'blob://');\n";
		w.resultingStr = str;
		return w; 
	}

	public static Window THistoryPushState_2(Window w){
		String str = "history.pushstate('',''," + w.url + ");\n";
		w.resultingStr = str;
		return w;
	}

	public static Window THistoryPushState_3(Window w){
		String str = "history.pushstate('','','" + targetDomain + "');\n";
		w.resultingStr = str;
		return w;
	}

	public static Window TSandbox(Window w){
		String str = "document.getElementById('" + w.frame + "').sandbox=\"" + "allow-scripts allow-modals allow-popups allow-popups-to-escape-sandbox" + "\";\n";
		w.resultingStr = str;
		return w;

	}

	public static Window TDocumentWrite(Window w){
		String str = "document.getElementById('" + w.frame + "').contentDocument.write('<h1>document write of iframe</h1>');\n";
		w.resultingStr = str;
		return w;
	}

}