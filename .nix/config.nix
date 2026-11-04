{
  format = "1.0.0";

  attribute = "trocq";

  no-rocq-yet = true;

  default-bundle = "rocq-9.1";

  bundles = let
    common-bundles = {
      coq-elpi.job = true;
      trocq-std.main-job = true;
      trocq-hott.main-job = true;
    };
  in {
    "rocq-9.0" = {
      rocqPackages = { rocq-core.override.version = "9.0"; 
        rocq-elpi.override.version = "3.5.0";
	};
      coqPackages = common-bundles // { 
        coq.override.version = "9.0"; 
        coq-elpi.override.version = "3.5.0";
      };
    };
    "rocq-9.1" = {
      rocqPackages = { rocq-core.override.version = "9.1"; 
        rocq-elpi.override.version = "3.5.0";
	};
      coqPackages = common-bundles // {
        coq.override.version = "9.1";
        coq-elpi.override.version = "3.5.0";
	
      };
    };
    ## Trocq is broken on Rocq-master
    # "rocq-master" = {
    #   rocqPackages = {
    #     rocq-core.override.version = "master";
    #   };
    #   coqPackages = common-bundles // {
    #     coq-elpi.override.elpi-version = "3.4.2";
    #     coq-elpi.override.version = "master";
    #     coq.override.version = "master";
    #     trocq-hott.job = false; # HoTT isn't available yet for 9.1
    #     trocq-hott-examples.job = false; # HoTT isn't available yet for 9.1
    #     trocq.job = false; # depends on trocq-hott
    #   };
    # };
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
