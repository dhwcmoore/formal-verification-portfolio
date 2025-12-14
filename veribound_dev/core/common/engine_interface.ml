open Shared_types

module type CLASSIFICATION_ENGINE = sig
  val engine_name : string
  val precision_guarantee : string
  val performance_characteristics : string

  val parse_value : string -> float
  val classify : domain -> float -> string
  val confidence_level : domain -> float -> [ `High | `Medium | `Low ]
  val boundary_distance : domain -> float -> float
end
