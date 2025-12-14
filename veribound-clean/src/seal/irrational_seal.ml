open Yojson.Basic.Util

type result_entry = {
  category : string;
  lower : float;
  upper : float;
  verdict : string;
}

let compute_seal json_content =
  let json = Yojson.Basic.from_string json_content in
  let results_json = json |> member "results" |> to_list in
  let results_text = Yojson.Basic.pretty_to_string (`List results_json) in
  let hash = Digestif.SHA256.digest_string results_text in
  Digestif.SHA256.to_hex hash
