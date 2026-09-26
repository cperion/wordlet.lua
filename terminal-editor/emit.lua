-- Run the checkout compiler without depending on the ignored distribution bundle.
package.path = "../?.lua;../?/init.lua;" .. package.path
os.exit(require("wordlet.cli")(require("wordlet"), arg) or 0)
