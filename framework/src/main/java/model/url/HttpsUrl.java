package model.url;

public class HttpsUrl extends Url {
	
	public Domain domain;
	public String path;
	
	public static final String xFrameCorresponding = "https://www.google.com";
	
	public HttpsUrl(String name) {
		super(name);
		this.scheme = Scheme.Https;
		this.corresponding = "https://example.com";
		this.correspondingOrigin = "https://example.com";
		
	}

}
