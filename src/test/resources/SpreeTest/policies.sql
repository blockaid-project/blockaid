-- The policy assumes there's only one store.
-- Initially the policy accommodated multiple stores, but some of the cache keys don't encode the store id,
-- (e.g.,`available-option-types/1637655325.2586029/1638315781.447258/en/USD/true/false/categories/men`),
-- so I'm not sure how the application loads the cache key corresponding to the current store...

SELECT `schema_migrations`.*
FROM `schema_migrations`;

-- We keep the `new_order_notifications_email` field non-public -- it's probably the store admin's email.
SELECT `id`,
       `name`,
       `url`,
       `meta_description`,
       `meta_keywords`,
       `seo_title`,
       `mail_from_address`,
       `default_currency`,
       `code`,
       `default`,
       `created_at`,
       `updated_at`,
       `supported_currencies`,
       `facebook`,
       `twitter`,
       `instagram`,
       `default_locale`,
       `customer_support_email`,
       `default_country_id`,
       `description`,
       `address`,
       `contact_phone`,
       `checkout_zone_id`,
       `seo_robots`,
       `supported_locales`
FROM `spree_stores`;

-- Information on deleted users shouldn't be accessible.
SELECT `spree_users`.*
FROM `spree_users`
WHERE `spree_users`.`deleted_at` IS NULL
  AND `spree_users`.`id` = _MY_UID;

-- The token is stored as a signed cookie and identifies the current order
-- (possibly from a user who is not signed in).
SELECT `spree_orders`.*
FROM `spree_orders`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_orders`.*
FROM `spree_orders`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- Spree returns different errors for (1) when an order number doesn't exist, and (2) when an order's number exists but
-- is not yours.  Have to make order numbers public.
SELECT `spree_orders`.`store_id`, `spree_orders`.`number`
FROM `spree_orders`;

SELECT `spree_role_users`.*
FROM `spree_role_users`
         INNER JOIN `spree_users` ON `spree_role_users`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
SELECT `spree_roles`.*
FROM `spree_roles`,
     `spree_role_users`,
     `spree_users`
WHERE `spree_roles`.`id` = `spree_role_users`.`role_id`
  AND `spree_role_users`.`user_id` = `spree_users`.`id`
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_preferences`.*
FROM `spree_preferences`;

-- TODO(zhangwen): Should we hide revoked access tokens or those that expire?
-- Here's an example query:
-- SELECT `spree_oauth_access_tokens`.* FROM `spree_oauth_access_tokens` WHERE `spree_oauth_access_tokens`.`resource_owner_id` = 2 AND `spree_oauth_access_tokens`.`revoked_at` IS NULL AND `spree_oauth_access_tokens`.`expires_in` IS NULL ORDER BY `spree_oauth_access_tokens`.`id` DESC LIMIT 1
SELECT `spree_oauth_access_tokens`.*
FROM `spree_oauth_access_tokens`
         INNER JOIN `spree_users` ON `spree_oauth_access_tokens`.`resource_owner_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_store_credits`.*
FROM `spree_store_credits`,
     `spree_users`
WHERE `spree_store_credits`.`deleted_at` IS NULL
  AND `spree_store_credits`.`user_id` = `spree_users`.`id`
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_addresses`.*
FROM `spree_addresses`
         INNER JOIN `spree_users` ON `spree_addresses`.`user_id` = `spree_users`.`id`
WHERE `spree_addresses`.`deleted_at` IS NULL
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- My own order's billing and shipping addresses are also visible.
-- I was going to add an integrity constraint saying that any address associated with my order are mine, but an
-- address's user ID is optional.
SELECT `spree_addresses`.*
FROM `spree_addresses`
         INNER JOIN `spree_orders` ON (`spree_addresses`.`id` = `spree_orders`.`bill_address_id` OR
                                       `spree_addresses`.`id` = `spree_orders`.`ship_address_id`)
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_addresses`.*
FROM `spree_addresses`
         INNER JOIN `spree_orders` ON (`spree_addresses`.`id` = `spree_orders`.`bill_address_id` OR
                                       `spree_addresses`.`id` = `spree_orders`.`ship_address_id`)
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_states`.*
FROM `spree_states`;
SELECT `spree_countries`.*
FROM `spree_countries`;

-- TODO(zhangwen): A homepage can be "not visible", but the fields of the `spree_cms_pages` table are still pretty
--   much visible (e.g., updated_at, seo_title).
SELECT `spree_cms_pages`.*
FROM `spree_cms_pages`
WHERE `spree_cms_pages`.`deleted_at` IS NULL
  AND (`spree_cms_pages`.`visible` = TRUE OR `spree_cms_pages`.`type` = 'Spree::Cms::Pages::Homepage');

SELECT `spree_menus`.*
FROM `spree_menus`;

SELECT `spree_menu_items`.*
FROM `spree_menu_items`;

SELECT `spree_cms_sections`.*
FROM `spree_cms_sections`,
     `spree_cms_pages`
WHERE `spree_cms_sections`.`cms_page_id` = `spree_cms_pages`.`id`
  AND `spree_cms_pages`.`deleted_at` IS NULL
  AND `spree_cms_pages`.`visible` = TRUE;

-- All Active Storage information is public.  According to documentation
-- (https://edgeguides.rubyonrails.org/active_storage_overview.html#public-access)
-- "All Active Storage controllers are publicly accessible by default. The generated URLs use a plain signed_id,
-- making them hard to guess but permanent. Anyone that knows the blob URL will be able to access it".
-- My testing indicates this to be the case in Spree as well.
SELECT `active_storage_attachments`.*
FROM `active_storage_attachments`;
SELECT `active_storage_blobs`.*
FROM `active_storage_blobs`;
SELECT `active_storage_variant_records`.*
FROM `active_storage_variant_records`;

SELECT `spree_taxonomies`.*
FROM `spree_taxonomies`;

SELECT `spree_taxons`.*
FROM `spree_taxons`;

SELECT `spree_products_stores`.*
FROM spree_products_stores
         INNER JOIN `spree_products` ON `spree_products`.`id` = `spree_products_stores`.`product_id`
WHERE (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

SELECT `spree_products_taxons`.*
FROM `spree_products_taxons`
         INNER JOIN `spree_products` ON `spree_products`.`id` = `spree_products_taxons`.`product_id`
WHERE (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

SELECT `spree_product_promotion_rules`.*
FROM `spree_product_promotion_rules`
         INNER JOIN `spree_products` ON `spree_products`.`id` = `spree_product_promotion_rules`.`product_id`
WHERE (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

-- Confirmed that Spree doesn't allow viewing products whose (1) `available_on` is null,
-- (2) `available_on` is later than the current time, or (3) `discontinue_on` is earlier than the current time.
SELECT `spree_products`.*
FROM `spree_products`
WHERE (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;
-- A product is also visible if one of its variants is in the cart / an order, even if it's unavailable or discontinued.
SELECT *
FROM `spree_products`
         INNER JOIN `spree_variants` ON `spree_products`.`id` = `spree_variants`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT *
FROM `spree_products`
         INNER JOIN `spree_variants` ON `spree_products`.`id` = `spree_variants`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

-- This separate view is needed for `products_for_filters_cache_key` -- the `for_filters` scope filters for all products
-- "active" in a currency, i.e., all products that have a variant whose price in the currency is not null.
-- The variants checked include discontinued ones!  This is an example of a "non-uniform" policy (since in other places
-- discontinued variants are not visible).
SELECT `spree_products`.`id`, `spree_products`.`updated_at`, `spree_prices`.`currency`
FROM `spree_products`
         INNER JOIN `spree_variants`
                    ON `spree_variants`.`deleted_at` IS NULL AND `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_prices`
                    ON `spree_prices`.`deleted_at` IS NULL AND `spree_prices`.`variant_id` = `spree_variants`.`id`
WHERE `spree_products`.`deleted_at` IS NULL
  AND (`spree_products`.discontinue_on IS NULL or `spree_products`.discontinue_on >= _NOW)
  AND (`spree_products`.available_on <= _NOW)
  AND `spree_prices`.`amount` IS NOT NULL;
-- Similar situation for `OptionValue::for_products` -- discontinued variants are counted.
-- This query reveals the option values for each product active for each currency (for the `available-option-types`
-- cache read).
SELECT `spree_products`.`id`, `spree_prices`.`currency`, `spree_option_value_variants`.`option_value_id`
FROM `spree_products`
         INNER JOIN `spree_variants` ON `spree_variants`.`deleted_at` IS NULL AND
                                        `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_prices`
                    ON `spree_prices`.`deleted_at` IS NULL AND `spree_prices`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_option_value_variants` ON `spree_option_value_variants`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_option_values`
                    ON `spree_option_values`.`id` = `spree_option_value_variants`.`option_value_id`
         INNER JOIN `spree_option_types` ON `spree_option_types`.`id` = `spree_option_values`.`option_type_id`
WHERE `spree_option_types`.`filterable` = true
  AND `spree_products`.`deleted_at` IS NULL
  AND (`spree_products`.discontinue_on IS NULL or `spree_products`.discontinue_on > _NOW)
  AND `spree_products`.available_on <= _NOW
  AND `spree_prices`.`amount` IS NOT NULL;

-- Friendly slugs for products that are directly accessible.
SELECT `friendly_id_slugs`.*
FROM `friendly_id_slugs`
         INNER JOIN `spree_products` ON (`friendly_id_slugs`.`sluggable_id` = `spree_products`.`id` AND
                                         `friendly_id_slugs`.`sluggable_type` = 'Spree::Product')
WHERE `friendly_id_slugs`.`deleted_at` IS NULL
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

SELECT `spree_promotion_rules`.*
FROM `spree_promotion_rules`
         INNER JOIN `spree_product_promotion_rules`
                    ON `spree_promotion_rules`.`id` = `spree_product_promotion_rules`.`promotion_rule_id`
         INNER JOIN `spree_products` ON `spree_product_promotion_rules`.`product_id` = `spree_products`.`id`
WHERE (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

-- TODO(zhangwen): This is a monstrosity.  We need better ergonomics.
--   Something like: If a product is visible, so should its variants be.
SELECT `spree_promotions`.*
FROM `spree_promotions`
         INNER JOIN `spree_promotion_rules` ON `spree_promotions`.`id` = `spree_promotion_rules`.`promotion_id`
         INNER JOIN `spree_product_promotion_rules`
                    ON `spree_promotion_rules`.`id` = `spree_product_promotion_rules`.`promotion_rule_id`
         INNER JOIN `spree_products` ON `spree_product_promotion_rules`.`product_id` = `spree_products`.`id`
WHERE `spree_promotions`.`advertise` = TRUE
  AND (spree_promotions.starts_at IS NULL OR spree_promotions.starts_at <= _NOW)
  AND (spree_promotions.expires_at IS NULL OR spree_promotions.expires_at >= _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  -- The master variant is always visible, it seems.
  AND (`spree_variants`.`is_master` = TRUE
    -- Other variants are visible if not discontinued.
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` >= _NOW)
  AND `spree_products`.`deleted_at` IS NULL
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;
-- A variant is visible if it's in the user's order, even if the variant is discontinued / no longer available, etc.
-- In the discontinued / unavailable case, the "orders" page still lists the item and but says "out of stock".
SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- For any product in the user's order, its variants are also visible (e.g., product image).
-- TODO(zhangwen): sometimes the default variant is not the master variant; amend policy.
SELECT `mv`.*
FROM `spree_variants` `mv`
         INNER JOIN `spree_products` ON (`mv`.`product_id` = `spree_products`.`id` AND `mv`.`is_master` = TRUE)
         INNER JOIN `spree_variants` `ov` ON `spree_products`.`id` = `ov`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `ov`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `mv`.*
FROM `spree_variants` `mv`
         INNER JOIN `spree_products` ON (`mv`.`product_id` = `spree_products`.`id` AND `mv`.`is_master` = TRUE)
         INNER JOIN `spree_variants` `ov` ON `spree_products`.`id` = `ov`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `ov`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants`
                    ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                       `spree_assets`.`viewable_id` = `spree_variants`.`id`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  AND (`spree_variants`.`is_master` = TRUE
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` >= _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND (`spree_products`.available_on <= _NOW);
SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants`
                    ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                       `spree_assets`.`viewable_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants`
                    ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                       `spree_assets`.`viewable_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants` `mv` ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                                             `spree_assets`.`viewable_id` = `mv`.`id`
         INNER JOIN `spree_products` ON (`mv`.`product_id` = `spree_products`.`id` AND `mv`.`is_master` = TRUE)
         INNER JOIN `spree_variants` `ov` ON `spree_products`.`id` = `ov`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `ov`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_assets`.*
FROM `spree_assets`
         INNER JOIN `spree_variants` `mv` ON `spree_assets`.`viewable_type` = 'Spree::Variant' AND
                                             `spree_assets`.`viewable_id` = `mv`.`id`
         INNER JOIN `spree_products` ON (`mv`.`product_id` = `spree_products`.`id` AND `mv`.`is_master` = TRUE)
         INNER JOIN `spree_variants` `ov` ON `spree_products`.`id` = `ov`.`product_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `ov`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
SELECT `spree_assets`.*
FROM `spree_assets`
WHERE `spree_assets`.`viewable_type` = 'Spree::MenuItem';

-- Allow access to deleted prices because they can be used in calculating default prices.
SELECT `spree_prices`.*
FROM `spree_prices`
         INNER JOIN `spree_variants` ON `spree_prices`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  AND (`spree_variants`.`is_master` = TRUE
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` >= _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

-- These two tables don't seem sensitive.  In particular, they're not tied to any variant.
SELECT `spree_option_values`.*
FROM `spree_option_values`;
SELECT `spree_option_types`.*
FROM `spree_option_types`;

SELECT `spree_option_value_variants`.*
FROM `spree_option_value_variants`
         INNER JOIN `spree_variants` ON `spree_option_value_variants`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  AND (`spree_variants`.`is_master` = TRUE
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` >= _NOW)
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;
SELECT `spree_option_value_variants`.*
FROM `spree_option_value_variants`
         INNER JOIN `spree_variants` ON `spree_option_value_variants`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_option_value_variants`.*
FROM `spree_option_value_variants`
         INNER JOIN `spree_variants` ON `spree_option_value_variants`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_line_items`.*
FROM `spree_line_items`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_line_items`.*
FROM `spree_line_items`
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

-- Adjustments for orders.
-- TODO(zhangwen): Should the `eligible` column affect visibility?
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_orders` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Order' AND
                                       `spree_adjustments`.`adjustable_id` = `spree_orders`.`id`) OR
                                      `spree_adjustments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_orders` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Order' AND
                                       `spree_adjustments`.`adjustable_id` = `spree_orders`.`id`) OR
                                      `spree_adjustments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- Adjustments for line items.
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_line_items` ON (`spree_adjustments`.`adjustable_type` = 'Spree::LineItem' AND
                                           `spree_adjustments`.`adjustable_id` = `spree_line_items`.`id`)
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_line_items` ON (`spree_adjustments`.`adjustable_type` = 'Spree::LineItem' AND
                                           `spree_adjustments`.`adjustable_id` = `spree_line_items`.`id`)
         INNER JOIN `spree_orders` ON `spree_line_items`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- Adjustments for shipments.
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_shipments` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Shipment' AND
                                          `spree_adjustments`.`adjustable_id` = `spree_shipments`.`id`)
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_adjustments`.*
FROM `spree_adjustments`
         INNER JOIN `spree_shipments` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Shipment' AND
                                          `spree_adjustments`.`adjustable_id` = `spree_shipments`.`id`)
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

-- Promotion actions for shipping.
SELECT `spree_promotion_actions`.*
FROM `spree_promotion_actions`
         INNER JOIN `spree_adjustments` ON (`spree_adjustments`.`source_type` = 'Spree::PromotionAction' AND
                                            `spree_adjustments`.`source_id` = `spree_promotion_actions`.`id`)
         INNER JOIN `spree_shipments` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Shipment' AND
                                          `spree_adjustments`.`adjustable_id` = `spree_shipments`.`id`)
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_promotion_actions`.*
FROM `spree_promotion_actions`
         INNER JOIN `spree_adjustments` ON (`spree_adjustments`.`source_type` = 'Spree::PromotionAction' AND
                                            `spree_adjustments`.`source_id` = `spree_promotion_actions`.`id`)
         INNER JOIN `spree_shipments` ON (`spree_adjustments`.`adjustable_type` = 'Spree::Shipment' AND
                                          `spree_adjustments`.`adjustable_id` = `spree_shipments`.`id`)
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_stock_items`.*
FROM `spree_stock_items`
         INNER JOIN `spree_stock_locations` ON `spree_stock_locations`.`id` = `spree_stock_items`.`stock_location_id`
         INNER JOIN `spree_variants` ON `spree_variants`.`id` = `spree_stock_items`.`variant_id`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
WHERE `spree_stock_items`.`deleted_at` IS NULL
  AND `spree_stock_locations`.`active` = TRUE
  AND `spree_variants`.`deleted_at` IS NULL
  -- The master variant is always visible, it seems.
  AND (`spree_variants`.`is_master` = TRUE
    -- Other variants are visible if not discontinued.
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` >= _NOW)
  AND `spree_products`.`deleted_at` IS NULL
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;
SELECT `spree_stock_items`.*
FROM `spree_stock_items`
         INNER JOIN `spree_stock_locations` ON `spree_stock_locations`.`id` = `spree_stock_items`.`stock_location_id`
         INNER JOIN `spree_variants` ON `spree_variants`.`id` = `spree_stock_items`.`variant_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
WHERE `spree_stock_items`.`deleted_at` IS NULL
  AND `spree_stock_locations`.`active` = true
  AND `spree_orders`.`token` = _TOKEN;
SELECT `spree_stock_items`.*
FROM `spree_stock_items`
         INNER JOIN `spree_stock_locations` ON `spree_stock_locations`.`id` = `spree_stock_items`.`stock_location_id`
         INNER JOIN `spree_variants` ON `spree_variants`.`id` = `spree_stock_items`.`variant_id`
         INNER JOIN `spree_line_items` ON `spree_line_items`.`variant_id` = `spree_variants`.`id`
         INNER JOIN `spree_orders` ON `spree_orders`.`id` = `spree_line_items`.`order_id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_stock_items`.`deleted_at` IS NULL
  AND `spree_stock_locations`.`active` = true
  AND `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- Another instance of non-uniform policy -- when filtering for backorderable variants, all stock items of the variant
-- are considered, even those belonging to a stock location that is not active.
SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_stock_items` ON `spree_stock_items`.`deleted_at` IS NULL AND
                                           `spree_stock_items`.`variant_id` = `spree_variants`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  -- The master variant is always visible, it seems.
  AND (`spree_variants`.`is_master` = TRUE
    -- Other variants are visible if not discontinued.
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` >= _NOW)
  AND `spree_products`.`deleted_at` IS NULL
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW
  AND `spree_stock_items`.`backorderable` = TRUE;
-- Same for in-stock items.
SELECT `spree_variants`.*
FROM `spree_variants`
         INNER JOIN `spree_products` ON `spree_variants`.`product_id` = `spree_products`.`id`
         INNER JOIN `spree_stock_items` ON `spree_stock_items`.`deleted_at` IS NULL AND
                                           `spree_stock_items`.`variant_id` = `spree_variants`.`id`
WHERE `spree_variants`.`deleted_at` IS NULL
  -- The master variant is always visible, it seems.
  AND (`spree_variants`.`is_master` = TRUE
    -- Other variants are visible if not discontinued.
    OR `spree_variants`.`discontinue_on` IS NULL
    OR `spree_variants`.`discontinue_on` >= _NOW)
  AND `spree_products`.`deleted_at` IS NULL
  AND (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW
  AND (`spree_stock_items`.`count_on_hand` > 0 OR `spree_variants`.`track_inventory` = FALSE);

SELECT `spree_payments`.*
FROM `spree_payments`
         INNER JOIN `spree_orders` ON `spree_payments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_payments`.*
FROM `spree_payments`
         INNER JOIN `spree_orders` ON `spree_payments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

-- Payment method is visible for the current user's order.
-- TODO(zhangwen): Any sensitive columns?
SELECT `spree_payment_methods`.*
FROM `spree_payment_methods`
         INNER JOIN `spree_payments` ON `spree_payments`.`payment_method_id` = `spree_payment_methods`.`id`
         INNER JOIN `spree_orders` ON `spree_payments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_payment_methods`.*
FROM `spree_payment_methods`
         INNER JOIN `spree_payments` ON `spree_payments`.`payment_method_id` = `spree_payment_methods`.`id`
         INNER JOIN `spree_orders` ON `spree_payments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- Or if the method is active and displayed to front end.
-- https://dev-docs.spreecommerce.org/internals/payments#payment-method-visibility
-- TODO(zhangwen): When is a payment method not displayed in backend? Isn't the backend only accessible by an admin?
SELECT `spree_payment_methods`.*
FROM `spree_payment_methods`
WHERE `spree_payment_methods`.active = TRUE
  AND `spree_payment_methods`.`deleted_at` IS NULL
  AND `spree_payment_methods`.`display_on` IN ('both', 'front_end');

SELECT `spree_shipments`.*
FROM `spree_shipments`
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_shipments`.*
FROM `spree_shipments`
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_shipping_rates`.*
FROM `spree_shipping_rates`
         INNER JOIN `spree_shipments` ON `spree_shipping_rates`.`shipment_id` = `spree_shipments`.`id`
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_shipping_rates`.*
FROM `spree_shipping_rates`
         INNER JOIN `spree_shipments` ON `spree_shipping_rates`.`shipment_id` = `spree_shipments`.`id`
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;

SELECT `spree_shipping_methods`.*
FROM `spree_shipping_methods`
         INNER JOIN `spree_shipping_rates`
                    ON `spree_shipping_rates`.`shipping_method_id` = `spree_shipping_methods`.`id`
         INNER JOIN `spree_shipments` ON `spree_shipping_rates`.`shipment_id` = `spree_shipments`.`id`
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
WHERE `spree_orders`.`token` = _TOKEN;
SELECT `spree_shipping_methods`.*
FROM `spree_shipping_methods`
         INNER JOIN `spree_shipping_rates`
                    ON `spree_shipping_rates`.`shipping_method_id` = `spree_shipping_methods`.`id`
         INNER JOIN `spree_shipments` ON `spree_shipping_rates`.`shipment_id` = `spree_shipments`.`id`
         INNER JOIN `spree_orders` ON `spree_shipments`.`order_id` = `spree_orders`.`id`
         INNER JOIN `spree_users` ON `spree_orders`.`user_id` = `spree_users`.`id`
WHERE `spree_users`.`id` = _MY_UID
  AND `spree_users`.`deleted_at` IS NULL;
-- TODO(zhangwen): again, my understanding is that the backend is only accessible to admins, who have access to all?
SELECT `spree_shipping_methods`.*
FROM `spree_shipping_methods`
WHERE `spree_shipping_methods`.`display_on` IN ('both', 'front_end')
  AND `spree_shipping_methods`.`deleted_at` IS NULL;

SELECT `spree_zones`.*
FROM `spree_zones`;

SELECT `spree_tax_categories`.*
FROM `spree_tax_categories`
WHERE `spree_tax_categories`.`deleted_at` IS NULL;

SELECT `spree_product_properties`.*
FROM `spree_product_properties`
INNER JOIN `spree_products` ON `spree_product_properties`.`product_id` = `spree_products`.`id`
WHERE (`spree_products`.deleted_at IS NULL OR `spree_products`.deleted_at >= _NOW)
  AND (`spree_products`.discontinue_on IS NULL OR `spree_products`.discontinue_on >= _NOW)
  AND `spree_products`.available_on <= _NOW;

SELECT `spree_properties`.*
FROM `spree_properties`;
