package model.url;

public class HttpUrl extends Url {
	
	public Domain domain;
	public String path;
	
	public static final String xFrameCorresponding = "https://www.google.com";
	
	public HttpUrl(String name) {
		super(name);
		this.scheme = Scheme.Http;
		this.corresponding = "http://example.com";
		this.correspondingOrigin = "http://example.com";
	}

}
