package main;

import java.net.MalformedURLException;

import edu.mit.csail.sdg.alloy4.Err;
import exec.TestExecutor;
import trans.RunAlloy;

public class MainAdapter {

	public static void main(String[] args) throws MalformedURLException, Err, InterruptedException {
		
		
//		TestExecutor exe = new TestExecutor();
//		TestExecutor.executeSample();
		// RunAlloy.executeAlloyModel("models/url.als", "APIaccessible");
		TestExecutor.safariCameraAttack();
	}

}
